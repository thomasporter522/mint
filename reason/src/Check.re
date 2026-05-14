open Term;
open Print;
open Error;
open MLType;

module StringMap = Map.Make(String);
module IntMap = Map.Make(Int);

/* OL typing context: a binding is either an OL constructor (with full
   type signature and defSite for go-to-definition) or one of the ML
   forms. Defined up here because computeType and unify (below) consult
   it for type-level propagation. */

type fullType = (list((option(string), ol)), ol);

type binding =
  | OL(option(fullType), option(meta))
  | ML(mlType)
  | Builtin(string)
  | SchemaBinding(ml)
  /* CoerceBinding(idx, body): idx records source-order registration so
     subsume can iterate coerce procedures bottom-up (highest idx first). */
  | CoerceBinding(int, ml)
  | MetaLet(ml, mlType);

type context = StringMap.t(binding);

/* === Elaboration state (per-declaration) ===
   Underapplied OL constructors are elaborated by inserting metavariables
   for the missing leading arguments. Metas are solved by unification
   whenever two types are compared. Solutions are threaded through the
   check functionally (no refs); each top-level entry into OL checking
   (each decl, each schema-generated witness) gets a fresh state. */

/* Inlay-hint kinds. ImplicitArgs renders as `…` and shows ghost args of
   an underapplied head. Coerce renders as `°` at the boundary of the
   coerced subterm and shows the wrapping in its tooltip. */
type hintKind =
  | ImplicitArgs
  | Coerce;

type elabState = {
  solutions: IntMap.t(ol),
  /* Each meta's expected type at creation. When unification solves a
     meta, the solution's actual type must agree with this — driving
     transitive solving (e.g. solving `?A := B` where ?A's expected was
     `Ul ?l` and B has type `Ul l` propagates to `?l := l`). */
  metaTypes: IntMap.t(ol),
  nextMetaId: int,
  /* Where the elaborator inserted ghost args, anchored at the term
     former. Each entry is (head's source meta, list of inserted ghost
     meta IDs). At the decl boundary we check which IDs remain unsolved
     and emit one yellow squiggle per head whose ghost run isn't fully
     determined. Recording AT INSERTION POINT (not after-the-fact via
     AST walk) means we don't have to distinguish source positions from
     substituted-in foreign positions — the state is per-decl, so every
     entry here is from this decl's own elaboration. */
  ghostInsertions: list((meta, list(int))),
  /* Recursion budget for coercion attempts. Decremented each time
     subsume invokes a coerce procedure and recursively re-checks the
     wrapped term; zero blocks further coercion (prevents loops when a
     coercion's output still fails to typecheck and would re-fire). */
  coerceDepth: int,
  /* Per successful coercion: (anchor, metaIDs) where anchor is the
     coerced subject's source meta and metaIDs are the metas allocated
     during the re-check of the coerced wrapping. Mirrors
     `ghostInsertions` and feeds a "coercion not fully solved" warning
     when any metaID stays unsolved at the decl boundary. */
  coerceInsertions: list((meta, list(int))),
};

let maxCoerceDepth = 4;

let emptyElabState: elabState = {
  solutions: IntMap.empty,
  metaTypes: IntMap.empty,
  nextMetaId: 0,
  ghostInsertions: [],
  coerceDepth: maxCoerceDepth,
  coerceInsertions: [],
};

/* Allocate a fresh meta as a ghost subterm at the given source meta,
   recording the expected type for type-level propagation. */
let mkMeta = (state: elabState, expectedTy: ol, m: meta): (ol, elabState) => {
  let id = state.nextMetaId;
  let t: ol = {value: OLMeta(id), meta: {...m, ghost: true}};
  (
    t,
    {
      ...state,
      metaTypes: IntMap.add(id, expectedTy, state.metaTypes),
      nextMetaId: id + 1,
    },
  );
};

/* Walk solution chains: return the term a meta currently points to, or
   the meta itself if unsolved. Non-meta terms are returned unchanged. */
let rec follow = (sols: IntMap.t(ol), t: ol): ol =>
  switch (t.value) {
  | OLMeta(id) =>
    switch (IntMap.find_opt(id, sols)) {
    | Some(t') => follow(sols, t')
    | None => t
    }
  | _ => t
  };

/* Deep-resolve all metas in a term using the current solutions. Metas
   that remain unsolved survive as OLMeta in the result. */
let rec zonk = (sols: IntMap.t(ol), t: ol): ol => {
  let t = follow(sols, t);
  switch (t.value) {
  | OLAp(f, args) =>
    {...t, value: OLAp(zonk(sols, f), List.map(zonk(sols), args))}
  | _ => t
  };
};

/* Occurs check: does `t` mention meta `id`, walking through the current
   solution chain? Used to prevent cyclic solutions like `?id := f(?id)`,
   which would otherwise make `follow`/`zonk` loop forever. */
let rec occurs = (sols: IntMap.t(ol), id: int, t: ol): bool => {
  let t = follow(sols, t);
  switch (t.value) {
  | OLMeta(id') => id == id'
  | OLAp(f, args) =>
    occurs(sols, id, f) || List.exists(occurs(sols, id), args)
  | _ => false
  };
};

type holeInfo = {
  goal: ml,
  context,
};

type staticInfo = {
  errors: list(error),
  holes: list((int, holeInfo)),
  /* For each OL-side hole, the expected OL term at registration time —
     kept on the side so we can zonk it at the decl boundary (after any
     unification on metas reachable from the expected). The ml-embedded
     goal in `holes` collapses OLMeta -> Hole(User), losing the meta
     identity, so we can't zonk it post-facto. Indexed by hole offset. */
  pendingHoleGoals: list((int, ol)),
  /* Blocks (postulate / construct) where every decl is complete: hole-
     free types and witnesses, no semantic errors anywhere in the block,
     transitively-referenced decls also complete. Each entry is the
     block's full source meta; the IDE anchors a ✓ at the start (the
     `postulate` / `construct` keyword) and the bridge filters out
     blocks whose range overlaps a syntax error. */
  completeBlocks: list(meta),
  /* Inlay hints: (offset, hintKind, ghost terms) — anchored just before
     `offset`. Ghost terms carried (not rendered strings) so they can be
     zonked at the decl boundary against the local solutions map; the
     API boundary prints them. */
  inlayHints: list((int, hintKind, list(ol))),
  /* Definitions: (use, def) — for each OL identifier reference that
     resolves to an OL binding, the meta of the use and the meta of the
     declaration site. Drives go-to-definition. */
  definitions: list((meta, meta)),
  inferred: option(fullType),
  mlInferred: option(mlType),
  /* The input term reconstructed with elaboration applied — ghost args
     inserted into underapplied OLAps, recursive sub-elaborations
     incorporated. Per-call (like inferred); discarded by mergeInfos.
     checkDeclLine reads this to build the externally-visible binding so
     constructors expose the elaborated type, not the raw one. */
  elaborated: option(ol),
  /* Per-decl elaborated reconstructions, in declaration order. Each
     checkDeclLine appends a single entry. Merged by concatenation so
     `elaborateProgram` can re-emit a fully elaborated source. Decls
     with duplicate names appear here in order — unlike `bindings`,
     which collapses duplicates. */
  elaboratedDecls: list(decl),
  bindings: context,
};

let olHole: ol = mkOL(OLHole(User));
let mlHole: ml = mkML(Hole(Synthesized));
let fullHole: fullType = ([], olHole);

let emptyInfo = {errors: [], pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, elaborated: None, elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};

/* MetaLet definitions in definition order, for eval env construction.
   Set by Meta block processing, read by Construct block. */
let metaDefsRef: ref(list((string, ml))) = ref([]);

/* Per-program completeness map, indexed by decl name. A decl maps to
   true iff it has been verified hole-free, all upstream decls it refers
   to are complete, and (for construct decls) its witness is also hole-
   free. Reset at the start of `checkProgram`; populated as decls are
   processed in order. Reads/writes happen alongside the functional
   threading of state but the cross-block scope is most naturally a
   module-local ref, matching the existing `metaDefsRef` pattern. */
let completenessRef: ref(StringMap.t(bool)) = ref(StringMap.empty);

/* True if a term contains any hole-shaped subterm (user hole,
   synthesized hole, or unsolved meta). */
let rec olHasHoles = (t: ol): bool =>
  switch (t.value) {
  | OLHole(_) | OLMeta(_) => true
  | OLIdentifier(_) => false
  | OLAp(f, args) =>
    olHasHoles(f) || List.exists(olHasHoles, args)
  };

/* Collect names of OL identifiers in `t` that resolve to OL bindings
   in `outerCtx`. Local-only references (e.g. to a decl's own params)
   are filtered out — they aren't dependencies for completeness. */
let olCollectRefs = (t: ol, outerCtx: context): list(string) => {
  let rec go = (acc, t: ol) =>
    switch (t.value) {
    | OLIdentifier(name) =>
      switch (StringMap.find_opt(name, outerCtx)) {
      | Some(OL(_, _)) => [name, ...acc]
      | _ => acc
      }
    | OLAp(f, args) =>
      let acc = go(acc, f);
      List.fold_left(go, acc, args);
    | OLHole(_) | OLMeta(_) => acc
    };
  go([], t);
};

/* Conjunction over a list of dep names: every named decl must already
   be marked complete in completenessRef. Names not yet known (forward
   refs, which the term-language shouldn't permit) count as not-complete. */
let allRefsComplete = (refs: list(string)): bool =>
  List.for_all(
    name =>
      switch (StringMap.find_opt(name, completenessRef^)) {
      | Some(true) => true
      | _ => false
      },
    refs,
  );

let mergeBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let mergeInfos = (i1: staticInfo, i2: staticInfo): staticInfo => {
  errors: i1.errors @ i2.errors,

  holes: i1.holes @ i2.holes,
  pendingHoleGoals: i1.pendingHoleGoals @ i2.pendingHoleGoals,
  inlayHints: i1.inlayHints @ i2.inlayHints,
  definitions: i1.definitions @ i2.definitions,
  inferred: None,
  mlInferred: None,
  elaborated: None,
  elaboratedDecls: i1.elaboratedDecls @ i2.elaboratedDecls,
  completeBlocks: i1.completeBlocks @ i2.completeBlocks,
  bindings: mergeBindings(i1.bindings, i2.bindings),
};

let withErrors = (info, errs) => {...info, errors: info.errors @ errs};
let withBindings = (info, ctx) => {...info, bindings: mergeBindings(info.bindings, ctx)};

/* --- OL term resolution against an environment --- */

type env = StringMap.t(ol);
let emptyEnv: env = StringMap.empty;

/* Witness substitution: maps names to (param_names, witness_body).
   For parameterless decls, param_names is [].
   For (f (x:A)) with witness w, resolving (f arg) gives w[x:=arg]. */
type witnessEnv = StringMap.t((list(string), ml));
let emptyWitnessEnv: witnessEnv = StringMap.empty;

let rec resolve = (env: env, t: ol): ol =>
  if (StringMap.is_empty(env)) {
    t;
  } else {
    switch (t.value) {
    | OLIdentifier(v) =>
      switch (StringMap.find_opt(v, env)) {
      | Some(replacement) => replacement
      | None => t
      }
    | OLAp(f, args) =>
      {...t, value: OLAp(resolve(env, f), List.map(resolve(env), args))}
    | OLHole(_) | OLMeta(_) => t
    };
  }

/* Resolve OL term through witness env (param-aware substitution).
   Witnesses are ml values, so we embed the OL term into ML for substitution,
   but we need to resolve OL references. We resolve in the OL domain
   for identifiers with no params, and handle application for parameterized decls. */
and resolveWithParams = (wenv: witnessEnv, t: ol): ol =>
  if (StringMap.is_empty(wenv)) {
    t;
  } else {
    switch (t.value) {
    | OLIdentifier(v) =>
      switch (StringMap.find_opt(v, wenv)) {
      | Some(([], witness)) => mlToOL(witness)  /* parameterless: direct substitution */
      | _ => t
      }
    | OLAp({value: OLIdentifier(v), _} as f, args) =>
      switch (StringMap.find_opt(v, wenv)) {
      | Some((paramNames, witness)) when List.length(paramNames) > 0 =>
        /* Parameterized: substitute param names with resolved args in witness */
        let resolvedArgs = List.map(resolveWithParams(wenv), args);
        if (List.length(paramNames) == List.length(resolvedArgs)) {
          let paramEnv = List.fold_left2(
            (acc, pname, arg) => StringMap.add(pname, arg, acc),
            StringMap.empty,
            paramNames,
            resolvedArgs,
          );
          resolve(paramEnv, mlToOL(witness));
        } else {
          {...t, value: OLAp(f, resolvedArgs)}
        }
      | _ =>
        {...t, value: OLAp(resolveWithParams(wenv, f), List.map(resolveWithParams(wenv), args))}
      }
    | OLAp(f, args) =>
      {...t, value: OLAp(resolveWithParams(wenv, f), List.map(resolveWithParams(wenv), args))}
    | OLHole(_) | OLMeta(_) => t
    };
  }

/* Convert an ML expression to an OL term (inverse of embedOL).
   Used when witness terms (ml) need to be resolved in OL domain. */
and mlToOL = (t: ml): ol => {
  let value =
    switch (t.value) {
    | Hole(k) => OLHole(k)
    | Identifier(s) => OLIdentifier(s)
    | Ap(f, args) => OLAp(mlToOL(f), List.map(mlToOL, args))
    | _ => OLHole(Synthesized)
    };
  {value, meta: t.meta};
};

/* === Type-level propagation: computeType + unify === */

/* Compute the OL type of a term, given the current solutions map. Used
   for type-level propagation: when a meta is solved to a term, the
   meta's recorded expected type must agree with the term's actual type.
   Returns None when we can't determine the type (e.g. for non-OL
   bindings, user holes, or higher-order positions). */
let computeType =
        (state: elabState, ctxLookup: string => option(fullType), t: ol)
        : option(ol) => {
  let t = follow(state.solutions, t);
  switch (t.value) {
  | OLMeta(id) => IntMap.find_opt(id, state.metaTypes)
  | OLIdentifier(v) =>
    switch (ctxLookup(v)) {
    | Some(([], retType)) => Some(retType)
    | _ => None
    }
  | OLAp(f, args) =>
    switch (f.value) {
    | OLIdentifier(v) =>
      switch (ctxLookup(v)) {
      | Some((params, retType))
          when List.length(params) == List.length(args) =>
        let env =
          List.fold_left2(
            (acc, (paramName, _), arg) =>
              switch (paramName) {
              | Some(n) => StringMap.add(n, arg, acc)
              | None => acc
              },
            StringMap.empty,
            params,
            args,
          );
        Some(resolve(env, retType));
      | _ => None
      }
    | _ => None
    }
  | OLHole(_) => None
  };
};

/* Functional unification. Returns Some(updated state) on success, None
   on failure. Type-level propagation: when a meta is solved to a non-
   meta term, its recorded expected type is unified with the solving
   term's computed type — letting structural subterm constraints
   transitively solve other metas. */
/* Eager unification: a meta solution is committed the moment it's
   chosen, and we never roll back. The boolean return flag reports
   whether the structures actually matched; on a mismatch the caller
   emits an error, but the partial solutions accumulated up to that
   point stay in the returned state. */
/* Conflict = a pair of subterms that genuinely don't unify (different
   identifiers, different-arity Aps, etc.) Surfacing the pair at the
   exact point unify gives up means the displayed terms are always,
   themselves, inconsistent — the invariant we want from error
   reporting. The post-follow `a`/`b` are what was actually being
   compared, so that's what gets returned. */
let rec unify =
        (state: elabState, ctx: context, a: ol, b: ol)
        : (elabState, option((ol, ol))) => {
  let ctxLookup = (v) =>
    switch (StringMap.find_opt(v, ctx)) {
    | Some(OL(ft, _)) => ft
    | _ => None
    };
  let a = follow(state.solutions, a);
  let b = follow(state.solutions, b);
  let solveMeta = (state, id, term) =>
    /* Refuse to introduce a cyclic solution. Without this, a constraint
       like `?id ≡ f(?id)` records `id ↦ f(?id)` and any later `follow`
       through `id` spins forever. */
    if (occurs(state.solutions, id, term)) {
      (state, Some((a, b)));
    } else {
      /* If the meta has a recorded expected type but we can't compute
         the candidate's type (e.g. the candidate references an unbound
         identifier, or is itself a hole), don't commit the solution.
         The meta stays open, which round-trips as `?` in the
         elaborated source — keeping elaboration idempotent in the
         face of malformed substitutions. */
      switch (IntMap.find_opt(id, state.metaTypes), computeType(state, ctxLookup, term)) {
      | (Some(expectedTy), Some(actualTy)) =>
        let state' = {...state, solutions: IntMap.add(id, term, state.solutions)};
        unify(state', ctx, expectedTy, actualTy);
      | (Some(_), None) => (state, None)
      | (None, _) =>
        let state' = {...state, solutions: IntMap.add(id, term, state.solutions)};
        (state', None);
      };
    };
  switch (a.value, b.value) {
  | (OLMeta(idA), OLMeta(idB)) when idA == idB => (state, None)
  | (OLMeta(idA), OLMeta(idB)) =>
    let (lo, hi) = idA < idB ? (idA, idB) : (idB, idA);
    let aliased: ol = {value: OLMeta(lo), meta: defaultMeta};
    let state' = {...state, solutions: IntMap.add(hi, aliased, state.solutions)};
    switch (
      IntMap.find_opt(lo, state.metaTypes),
      IntMap.find_opt(hi, state.metaTypes),
    ) {
    | (Some(t1), Some(t2)) => unify(state', ctx, t1, t2)
    | _ => (state', None)
    };
  | (OLMeta(id), _) => solveMeta(state, id, b)
  | (_, OLMeta(id)) => solveMeta(state, id, a)
  | (OLHole(_), _) | (_, OLHole(_)) => (state, None)
  | (OLIdentifier(x), OLIdentifier(y)) when x == y => (state, None)
  | (OLAp(f1, args1), OLAp(f2, args2))
      when List.length(args1) == List.length(args2) =>
    /* Same head shape → drill into each arg, propagating the first
       sub-conflict (which is, by induction, an inconsistent pair).
       If the heads themselves disagree, the conflict belongs at the
       outer Ap level: showing `sym vs eq` loses context, so wrap to
       `(sym e) vs (eq … )`. */
    let (s, headErr) = unify(state, ctx, f1, f2);
    let (s', argsErr) =
      List.fold_left2(
        ((s, err), x, y) =>
          switch (err) {
          | Some(_) => (s, err)
          | None => unify(s, ctx, x, y)
          },
        (s, None),
        args1,
        args2,
      );
    switch (headErr, argsErr) {
    | (Some(_), _) => (s', Some((a, b)))
    | (None, e) => (s', e)
    };
  | _ => (state, Some((a, b)))
  };
};

/* --- Checking modes --- */

type checkingMode =
  | Program
  | Line
  | Spine
  | Argument
  | IdentifierMode
  | Expression(option(ol));

let stringOfMode =
  fun
  | Program => "program"
  | Line => "line"
  | Spine => "spine"
  | Argument => "argument"
  | IdentifierMode => "identifier"
  | Expression(_) => "expression";

/* --- Context lookup (OL mode) --- */

type lookupResult =
  | Found(option(fullType), option(meta))
  | NotFound;

let lookupCtx = (ctx: context, x: string): lookupResult =>
  switch (StringMap.find_opt(x, ctx)) {
  | Some(OL(ft, defSite)) => Found(ft, defSite)
  | Some(ML(_)) | Some(Builtin(_)) | Some(SchemaBinding(_)) | Some(CoerceBinding(_)) | Some(MetaLet(_, _)) => NotFound
  | None => NotFound
  };

/* --- Error helpers --- */

/* Subsume: type-equality check that may solve metas via unification.
   Returns the (possibly updated) elaboration state alongside any errors.
   Note: under-application is never an error at subsume — any caller
   that brings an inferred-with-params here has already chosen to use
   the partial form as-is, and the elaborator unconditionally inserts
   ghost metas at value positions, so a leftover param-typed inferred
   only reaches here from contexts (like OLAp head) where the partial
   shape is wanted. */
/* Coerce procedures registered in ctx, sorted bottom-up (highest idx
   first) so the most-recently-declared coercion is tried first. */
let collectCoerceBindings = (ctx: context): list((int, string, ml)) => {
  let xs =
    StringMap.fold(
      (name, binding, acc) =>
        switch (binding) {
        | CoerceBinding(idx, body) => [(idx, name, body), ...acc]
        | _ => acc
        },
      ctx, [],
    );
  List.sort(((i1, _, _), (i2, _, _)) => compare(i2, i1), xs);
};

let checkArity = (expected, found, from, to_) =>
  if (expected == found) {
    [];
  } else {
    let msg = expected > found ? "Too few arguments" : "Too many arguments";
    [mark(msg, from, to_)];
  };

let ensureMode = (allowed, mode, from, to_) =>
  if (List.mem(stringOfMode(mode), allowed)) {
    [];
  } else {
    let allowedStr = String.concat(",", allowed);
    [mark(
       "Sort error (expected "
       ++ allowedStr
       ++ ", found "
       ++ stringOfMode(mode)
       ++ ")",
       from, to_,
     )];
  };

/* === Elaboration: ghost-subterm machinery ===

   An "elaborated" OL term is a term where some subterms were synthesized
   by the checker rather than written by the user. Such subterms have
   meta.ghost = true. The genericity is in the flag: anything you mark
   ghost — a hole inserted as an implicit argument, a wrapper inserted
   to coerce a subterm, a body inserted to fill a user hole — flows
   through the same inlay-hint pipeline. */

let mkGhost = (v: cOL): ol => {value: v, meta: asGhost(defaultMeta)};

/* Print a (zonked) ghost subterm for inlay-hint display. After zonking,
   surviving OLMeta(_) subterms are unsolved metavariables and render as
   "?". OLHole(_) cases (synthesized or user-written holes that ended up
   in a ghost slot) also render as "?" — the user never sees meta IDs. */
let rec printGhost = (t: ol): string =>
  switch (t.value) {
  | OLHole(_) | OLMeta(_) => "?"
  | OLIdentifier(s) => s
  | OLAp(f, args) =>
    let inside =
      printGhost(f) ++ " " ++ String.concat(" ", List.map(printGhost, args));
    t.meta.parens ? "(" ++ inside ++ ")" : inside;
  };

/* Top-level rendering of one ghost term in an inlay-hint sequence.
   Unlike printGhost, this always wraps compound (OLAp) results in
   parens, so a list of ghosts joined by spaces stays unambiguous —
   `? ? (Ul l5) ?` rather than `? ? Ul l5 ?`. */
let renderGhostInline = (t: ol): string =>
  switch (t.value) {
  | OLAp(_, _) =>
    "(" ++ printGhost({...t, meta: {...t.meta, parens: false}}) ++ ")"
  | _ => printGhost(t)
  };

/* Build the U+2026 ellipsis as a real JS 1-char string. Writing "…"
   on the OCaml side surfaces as three Latin-1-mapped chars (the UTF-8
   bytes) at the Melange→JS boundary; constructing it via JS gives a
   proper single-codepoint string. */
[@mel.scope "String"] external _fromCharCode: int => string = "fromCharCode";
let ellipsis = _fromCharCode(0x2026);
/* U+02DA RING ABOVE — narrower than U+00B0 DEGREE SIGN. Reads as a
   "coerced" marker without the typographic weight of the math degree. */
let degree = _fromCharCode(0x02DA);
let boxChar = _fromCharCode(0x25A1);

/* The full values rendering of a ghost run: each ghost printed (compounds
   in parens), joined by spaces. Used both for the partially-unsolved
   label and for the always-on hover tooltip. */
let renderHintValues = (ghosts: list(ol)): string =>
  String.concat(" ", List.map(renderGhostInline, ghosts));

/* Displayed label, by kind. ImplicitArgs renders a single ellipsis (one
   visual unit regardless of how many ghost args); Coerce renders a
   degree sign sitting just past the coerced subterm. */
let renderHintLabel = (kind: hintKind, _ghosts: list(ol)): string =>
  switch (kind) {
  | ImplicitArgs => ellipsis
  | Coerce => degree
  };

/* Walk an arg list and emit one entry per maximal run of ghost args.
   The leading run is anchored just after the head `f`'s end position so
   the rendered ellipsis sits immediately after the term former,
   independent of any whitespace between f and the first user arg.
   Subsequent runs are anchored at the start of the following non-ghost
   arg (so they sit just before that arg). A trailing ghost run with no
   following non-ghost (e.g. `(C)` parsed as OLAp(C, []) → all leading
   ghosts after elaboration) is flushed at end-of-args with the same
   leading-run anchor. */
/* An underapplication-inserted implicit arg is always a bare OLMeta —
   distinct from a coerce-wrapped arg whose outer node is ghost-flagged
   but is structurally an OLAp. */
let isImplicitGhost = (a: ol): bool =>
  a.meta.ghost
  && (
    switch (a.value) {
    | OLMeta(_) => true
    | _ => false
    }
  );

let extractArgRunHints =
    (f: ol, args: list(ol)): list((int, hintKind, list(ol))) =>
  /* When `f` itself is ghost (e.g. an OLAp nested inside a coerce
     wrapping), the whole spine belongs to a synthesized wrapper that
     already has its own `˚` hint at the subject — don't double-surface
     its args with `…` hints. */
  if (f.meta.ghost) {
    [];
  } else {
  let rec go =
          (acc: list((int, hintKind, list(ol))), run: list(ol), seenNonGhost: bool,
           args: list(ol))
          : list((int, hintKind, list(ol))) =>
    switch (args) {
    | [] =>
      if (run == []) {
        List.rev(acc);
      } else {
        List.rev([(f.meta.end_, ImplicitArgs, List.rev(run)), ...acc]);
      }
    | [a, ...rest] =>
      if (isImplicitGhost(a)) {
        go(acc, [a, ...run], seenNonGhost, rest);
      } else if (run != []) {
        let anchor = seenNonGhost ? a.meta.start : f.meta.end_;
        go([(anchor, ImplicitArgs, List.rev(run)), ...acc], [], true, rest);
      } else {
        go(acc, [], true, rest);
      }
    };
  go([], [], false, args);
  };

/* --- Extracting params (name + type) from OL arg list --- */

/* === ML type utilities === */

let addParens = (t: ml): ml =>
  switch (t.value) {
  | Identifier(_) => t
  | _ => {...t, meta: {...t.meta, parens: true}}
  };

let rec mlTypeToTerm = (ty: mlType): ml =>
  switch (ty) {
  | MTerm => mkML(Identifier("Term"))
  | MSort => mkML(Identifier("Sort"))
  | MBool => mkML(Identifier("Bool"))
  | MString => mkML(Identifier("String"))
  | MList(t) => mkML(Ap(mkML(Identifier("List")), [addParens(mlTypeToTerm(t))]))
  | MResult(t) => mkML(Ap(mkML(Identifier("Result")), [addParens(mlTypeToTerm(t))]))
  | MTuple(items) => {
      let t = mkML(Tuple(List.map(mlTypeToTerm, items)));
      {...t, meta: {...t.meta, parens: true}};
    }
  | MArrow(a, b) => mkML(Ap(mkML(Identifier("->")), [addParens(mlTypeToTerm(a)), addParens(mlTypeToTerm(b))]))
  };

/* Set both inferred (OL fullType for display) and mlInferred (exact ML type).
   Used as: setMlType(info, ty) */
let setMlType = (info: staticInfo, ty: mlType): staticInfo =>
  {...info,
    inferred: Some(([], mlToOL(mlTypeToTerm(ty)))),
    mlInferred: Some(ty)};

let mlSubsume = (expected: mlType, got: mlType, from, to_): list(error) =>
  if (eqType(expected, got)) {
    [];
  } else {
    [mark(
      "Expected " ++ printType(expected) ++ ", got " ++ printType(got),
      from, to_,
    )];
  };

/* Convert an ML expression to an mlType (for parsing type expressions in ML context) */
let rec mlExprToType = (t: ml): option(mlType) =>
  switch (t.value) {
  | Identifier("Term") => Some(MTerm)
  | Identifier("Sort") => Some(MSort)
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Signature") =>
    Some(MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm]))
  | Ap({value: Identifier("List"), _}, [arg]) =>
    switch (mlExprToType(arg)) {
    | Some(t) => Some(MList(t))
    | None => None
    }
  | Ap({value: Identifier("Result"), _}, [arg]) =>
    switch (mlExprToType(arg)) {
    | Some(t) => Some(MResult(t))
    | None => None
    }
  | Ap({value: Identifier("->"), _}, [l, r]) =>
    switch (mlExprToType(l), mlExprToType(r)) {
    | (Some(lt), Some(rt)) => Some(MArrow(lt, rt))
    | _ => None
    }
  | Tuple(items) =>
    let types = List.map(mlExprToType, items);
    if (List.for_all(t => t != None, types)) {
      Some(MTuple(List.map(t => switch (t) { | Some(v) => v | None => MTerm }, types)))
    } else {
      None
    }
  | _ => None
  };

/* Extract ML type from inferred, defaulting to MTerm */
let getInferredMlType = (info: staticInfo): mlType =>
  switch (info.mlInferred) {
  | Some(ty) => ty
  | None => MTerm
  };

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

let hasOLBindings = (ctx: context): bool =>
  StringMap.exists(
    (_, v) => switch (v) { | OL(_, _) => true | _ => false },
    ctx,
  );

/* Signature = (Term, List (Term, Term), Term) — name, params, return type.
   Matches Eval.declToSignature: Tuple([name, List(params), retType]) */
let signatureType = MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm]);

/* Schema type: a curried function taking the outer scope's signatures
   first, then the construct block's signatures, returning a Result-list
   of witnesses. The outer scope lets schemas introspect available
   constructors (e.g. find a type's eliminator by inspecting types). */
let schemaType =
  MArrow(MList(signatureType), MArrow(MList(signatureType), MResult(MList(MTerm))));

/* Coerce type: ctx -> expected -> found -> contents -> Result Term.
   Invoked by `subsume` on inconsistency: the procedure may wrap the
   inferred subterm with a coercion (e.g. cast through an equality),
   and the result is re-checked against the expected type. */
let coerceType =
  MArrow(
    MList(signatureType),
    MArrow(MTerm, MArrow(MTerm, MArrow(MTerm, MResult(MTerm)))),
  );

/* ML builtins context — every ML builtin must be declared here.
   No OL-level built-ins: the OL context begins empty, so Sort must be
   declared by the user (typically `Sort : Sort` at the top of the first
   postulate block). */
let mlBuiltins: context =
  List.fold_left(
    (acc, (name, b)) => StringMap.add(name, b, acc),
    StringMap.empty,
    [
      /* Polymorphic builtins — need custom typing rules */
      ("fst", Builtin("fst")),
      ("snd", Builtin("snd")),
      ("foldl", Builtin("foldl")),
      ("apply", Builtin("apply")),
      /* Monomorphic builtins */
      ("true", ML(MBool)),
      ("false", ML(MBool)),
      ("Ok", Builtin("Ok")),
      ("Error", Builtin("Error")),
    ],
  );

/* === Unified checker: OL and ML mutually recursive === */

/* Zonk all ghost terms in an info's inlay hints with the given solutions.
   Called at decl/witness boundaries so the per-decl solutions are applied
   before the state is discarded. */
let zonkInlayHints =
    (sols: IntMap.t(ol), info: staticInfo): staticInfo => {
  let zonked =
    List.map(
      ((pos, kind, ghosts)) => (pos, kind, List.map(zonk(sols), ghosts)),
      info.inlayHints,
    );
  {...info, inlayHints: zonked};
};

/* Rebuild each OL-side hole's ml goal from its pending ol expected,
   zonked against the final per-decl solutions. Holes whose offset isn't
   in pendingHoleGoals (e.g. ML-side `Hole` registrations) are left
   alone. After this pass, pendingHoleGoals is cleared. */
let resolveHoleGoals =
    (sols: IntMap.t(ol), info: staticInfo): staticInfo => {
  let pendingMap =
    List.fold_left(
      (acc, (pos, olGoal)) => IntMap.add(pos, olGoal, acc),
      IntMap.empty,
      info.pendingHoleGoals,
    );
  let updated =
    List.map(
      ((pos, hi: holeInfo)) =>
        switch (IntMap.find_opt(pos, pendingMap)) {
        | Some(olGoal) =>
          (pos, {...hi, goal: embedOL(zonk(sols, olGoal))})
        | None => (pos, hi)
        },
      info.holes,
    );
  {...info, holes: updated, pendingHoleGoals: []};
};

/* Walk an already-zonked elaborated term and emit one warning per
   OLAp head whose elaborator-inserted ghost args didn't all get
   solved. A ghost arg is identified by its meta.ghost flag (set by
   mkMeta when the elaborator allocated the meta); user-written `?`s
   carry ghost=false, so they don't trigger this — leaving the source
   `?` semantics intact while still flagging incomplete inferred
   spines. Warnings are non-idempotent across re-elaboration (round 1
   inserts ghosts; round 2 sees the user-`?` they printed back to,
   which don't carry ghost=true) but errors stay idempotent. */
/* Emit one warning per term-former whose elaborator-inserted ghost
   args didn't all get solved. Reads `state.ghostInsertions`, which is
   appended to at each insertion site (OLAp underapplication and bare
   identifier-with-params), pairing the head's source meta with the IDs
   of the inserted ghost metas. At the decl boundary we check which IDs
   remain unsolved (their `zonk` still surfaces as OLMeta) and emit a
   warning anchored at the head.

   Why drive this off recorded insertions rather than walking the
   elaborated AST: elaboration is per-decl (`emptyElabState` per
   `checkDeclLine`), so every entry in `ghostInsertions` is from THIS
   decl's elaboration. Walking the post-elaboration AST would mix in
   substituted-in fragments from other decls' bindings (with foreign
   source positions) and require ad-hoc filtering to suppress them. */
let collectGhostWarnings = (state: elabState): list(error) => {
  let isUnsolved = (id: int) => {
    let probe: ol = {value: OLMeta(id), meta: defaultMeta};
    switch (zonk(state.solutions, probe).value) {
    | OLMeta(_) => true
    | _ => false
    };
  };
  List.filter_map(
    ((headMeta, ids): (meta, list(int))) =>
      List.exists(isUnsolved, ids)
        ? Some(Error.warn(
            "Implicit arguments not fully solved",
            headMeta.start, headMeta.end_,
          ))
        : None,
    state.ghostInsertions,
  );
};

let collectCoerceWarnings = (state: elabState): list(error) => {
  let isUnsolved = (id: int) => {
    let probe: ol = {value: OLMeta(id), meta: defaultMeta};
    switch (zonk(state.solutions, probe).value) {
    | OLMeta(_) => true
    | _ => false
    };
  };
  List.filter_map(
    ((anchor, ids): (meta, list(int))) =>
      List.exists(isUnsolved, ids)
        ? Some(Error.warn(
            "Coercion not fully solved",
            anchor.start, anchor.end_,
          ))
        : None,
    state.coerceInsertions,
  );
};

/* Zonk a term and replace any surviving (unsolved) metas with user
   holes. Used to clean up a per-decl elaborated term before it's stored
   in an externally-visible binding: meta IDs are decl-local and would
   be meaningless across decl boundaries. OLHole(User) round-trips
   through printing as "?", which the parser turns back into OLHole(User)
   — the elaborator then re-allocates a meta, achieving idempotence at
   the source-text level. */
let rec zonkAndForgetMetas = (sols: IntMap.t(ol), t: ol): ol => {
  let t = zonk(sols, t);
  switch (t.value) {
  | OLMeta(_) => {...t, value: OLHole(User)}
  | OLAp(f, args) =>
    {
      ...t,
      value:
        OLAp(
          zonkAndForgetMetas(sols, f),
          List.map(zonkAndForgetMetas(sols), args),
        ),
    }
  | _ => t
  };
};

/* Shadow check: if `name` is already bound in `ctx`, emit a warning at
   `nameMeta`. If the shadowed binding has a known source position (OL
   bindings carry a defSite), also emit a definition link so ctrl-click
   on the shadowing name jumps to the shadowed binding. */
let shadowCheck =
    (name: string, nameMeta: meta, ctx: context)
    : (list(error), list((meta, meta))) =>
  switch (StringMap.find_opt(name, ctx)) {
  | None => ([], [])
  | Some(b) =>
    let warns = [
      Error.warn("Shadows existing binding", nameMeta.start, nameMeta.end_),
    ];
    let defs =
      switch (b) {
      | OL(_, Some(dm)) => [(nameMeta, dm)]
      | _ => []
      };
    (warns, defs);
  };

/* Project every OL binding in `ctx` into a schema-input signature
   (same shape as Eval.declToSignature produces for construct decls):
   `(name, [(p, ty)...], retType)` as an ml tuple. ML / Builtin /
   schema / metaLet bindings are skipped — they're not OL constructors. */
let bindingsToSignatures = (ctx: context): list(ml) =>
  StringMap.fold(
    (name, b, acc) =>
      switch (b) {
      | OL(Some((params, retType)), _) =>
        let nameTerm = mkML(Identifier(name));
        let paramTuples =
          List.map(
            ((pname, ty)) => {
              let pnameTerm =
                switch (pname) {
                | Some(n) => mkML(Identifier(n))
                | None => mkML(Hole(Synthesized))
                };
              mkML(Tuple([pnameTerm, embedOL(ty)]));
            },
            params,
          );
        let sig_ =
          mkML(
            Tuple([nameTerm, mkML(List(paramTuples)), embedOL(retType)]),
          );
        [sig_, ...acc];
      | _ => acc
      },
    ctx,
    [],
  );

/* Check a single declaration line: (name (p1:T1) ...) : RetType.
   Per-decl elaboration state is created here, threaded through every
   sub-check, and consumed at the end via zonkInlayHints. Solutions
   never escape this scope. */
let coerceSentinelName = "__coerce_subject__";

/* Substitute the original `contents` term back into the procedure's
   result wherever the sentinel identifier appears, and mark every other
   node (the wrapping) as ghost. Result tree: outer wrapping is ghost,
   inner subterm is the unghosted user content. */
let rec substituteAndGhost = (contents: ol, t: ol): ol =>
  switch (t.value) {
  | OLIdentifier(n) when n == coerceSentinelName => contents
  | OLAp(f, args) =>
    let f' = substituteAndGhost(contents, f);
    let args' = List.map(substituteAndGhost(contents), args);
    {value: OLAp(f', args'), meta: {...t.meta, ghost: true}}
  | _ => {...t, meta: {...t.meta, ghost: true}}
  };

/* Same shape walk but only substitutes — for tooltip rendering, where
   we want the wrapping shown with the subject replaced by a placeholder
   (box) rather than duplicated. No ghost flagging. */
let rec substituteOnly = (replacement: ol, t: ol): ol =>
  switch (t.value) {
  | OLIdentifier(n) when n == coerceSentinelName => replacement
  | OLAp(f, args) =>
    let f' = substituteOnly(replacement, f);
    let args' = List.map(substituteOnly(replacement), args);
    {...t, value: OLAp(f', args')}
  | _ => t
  };

let rec subsume =
    (state: elabState,
     ctx: context,
     expected: option(ol),
     inferred: option(fullType),
     subterm: option(ol),
     from, to_)
    : (list(error), elabState, option(ol), list((int, hintKind, list(ol)))) => {
  let inferredOut = Option.map(((_, out)) => out, inferred);
  switch (expected, inferredOut) {
  | (Some(exp), Some(inf)) =>
    let (s, conflict) = unify(state, ctx, exp, inf);
    /* Keep the post-unify state on failure so metas committed before
       the mismatch stay solved. The message reports the top-level
       expected and inferred types — not unify's drilled-down conflict
       subterms — zonked against the final state. */
    switch (conflict) {
    | None => ([], s, None, [])
    | Some(_) =>
      let coerceCandidates = collectCoerceBindings(ctx);
      let canCoerce =
        switch (subterm) {
        | Some(_) when s.coerceDepth > 0 && coerceCandidates != [] => true
        | _ => false
        };
      if (canCoerce) {
        switch (tryCoercions(s, ctx, exp, inf, Option.get(subterm), coerceCandidates)) {
        | Some((newState, coercedTerm, hints)) =>
          ([], newState, Some(coercedTerm), hints)
        | None =>
          ([mark(
             "Inconsistency (expected "
             ++ printOL(zonk(s.solutions, exp))
             ++ ", got "
             ++ printOL(zonk(s.solutions, inf))
             ++ ")",
             from, to_,
           )], s, None, [])
        };
      } else {
        ([mark(
           "Inconsistency (expected "
           ++ printOL(zonk(s.solutions, exp))
           ++ ", got "
           ++ printOL(zonk(s.solutions, inf))
           ++ ")",
           from, to_,
         )], s, None, []);
      };
    };
  | _ => ([], state, None, [])
  };
}

and tryCoercions =
    (state: elabState,
     ctx: context,
     expected: ol,
     found: ol,
     contents: ol,
     candidates: list((int, string, ml)))
    : option((elabState, ol, list((int, hintKind, list(ol))))) =>
  switch (candidates) {
  | [] => None
  | [(_idx, _name, body), ...rest] =>
    let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
    let evalEnv =
      StringMap.fold(
        (name, binding, acc) =>
          switch (binding) {
          | MetaLet(rhs, _) =>
            switch (Eval.evalExpr(acc, rhs)) {
            | Ok(v) => StringMap.add(name, v, acc)
            | _ => acc
            }
          | _ => acc
          },
        mlCtx, StringMap.empty,
      );
    switch (Eval.evalExpr(evalEnv, body)) {
    | Err(_) => tryCoercions(state, ctx, expected, found, contents, rest)
    | Ok(procVal) =>
      let outerSigs = bindingsToSignatures(ctx);
      let zExp = zonk(state.solutions, expected);
      let zFound = zonk(state.solutions, found);
      let zContents = zonk(state.solutions, contents);
      /* Pass a sentinel identifier as `contents` to the procedure so we
         can locate the user's subterm in the procedure's result and
         distinguish it from the synthesised wrapping. */
      let sentinel: ol = {
        value: OLIdentifier(coerceSentinelName),
        meta: defaultMeta,
      };
      switch (Eval.runCoerce(procVal, outerSigs, zExp, zFound, sentinel)) {
      | CoerceFailed(_) => tryCoercions(state, ctx, expected, found, contents, rest)
      | Coerced(mlResult) =>
        /* Convert the procedure's ML result back to OL, substitute the
           real contents back into the sentinel position, mark the rest
           ghost, then re-check at the expected type. */
        let rawOL = mlToOL(mlResult);
        let coercedInner = substituteAndGhost(zContents, rawOL);
        /* Force parens at the root so when this replaces the user's
           subterm as an argument it doesn't flatten into the parent's
           spine on print/round-trip. */
        let coerced: ol = {
          ...coercedInner,
          meta: {...coercedInner.meta, parens: true},
        };
        let stateDec = {...state, coerceDepth: state.coerceDepth - 1};
        let metasBefore = stateDec.nextMetaId;
        let (info, newState) =
          checkOLTerm(stateDec, ctx, Expression(Some(expected)), coerced);
        if (info.errors == []) {
          let final =
            switch (info.elaborated) {
            | Some(t) => t
            | None => coerced
            };
          /* Anchor the `°` sigil just before the user's subterm; tooltip
             shows the wrapping with the subject replaced by a `□` box,
             so the user's source text isn't duplicated. */
          let boxOL: ol = {
            value: OLIdentifier(boxChar),
            meta: defaultMeta,
          };
          let tooltipTree = substituteOnly(boxOL, rawOL);
          let hint = (zContents.meta.start, Coerce, [tooltipTree]);
          /* Record the meta IDs allocated by the wrapping's re-check so
             a "Coercion not fully solved" warning fires at the subject
             if any stays unsolved at the decl boundary. */
          let metasAfter = newState.nextMetaId;
          let wrappingMetaIds =
            metasAfter > metasBefore
              ? List.init(metasAfter - metasBefore, i => metasBefore + i)
              : [];
          let newState =
            wrappingMetaIds == []
              ? newState
              : {
                  ...newState,
                  coerceInsertions:
                    newState.coerceInsertions @ [(zContents.meta, wrappingMetaIds)],
                };
          Some((newState, final, info.inlayHints @ [hint]));
        } else {
          tryCoercions(state, ctx, expected, found, contents, rest);
        };
      };
    };
  }

and checkDeclLine = (ctx: context, d: decl): staticInfo => {
  /* Matches typeDeclaration in the formalism:
       typeArgs(Γ[x ā : T])(ā)
       typeTerm(Γ[x ā : T][ā])(T)(T')
       ⊢ typeDeclaration(Γ)(x ā : T)
     The declaration x ā : T is added to Γ before checking its own
     parameter types and return type, so the constructor's name is in
     scope inside its own signature. Each parameter's type is itself
     checked as a well-formed term; the parameter binding is added to
     the context before the next parameter is checked, supporting
     dependent parameter types. */
  let rawParamPairs =
    List.map((p: param) => (Some(p.paramName), p.paramType), d.params);
  /* Self-binding for in-decl recursive reference uses the raw types — the
     decl's signature can refer to itself but elaboration of those uses
     happens fresh through checkOLTerm. */
  let inDeclSelfBinding = OL(Some((rawParamPairs, d.retType)), Some(d.nameMeta));
  let selfCtx = StringMap.add(d.declName, inDeclSelfBinding, ctx);
  let (selfShadowWarns, selfShadowDefs) =
    shadowCheck(d.declName, d.nameMeta, ctx);
  /* typeArgs: check each param's type, threading the elaboration state.
     Capture each paramType's elaborated form for the external binding. */
  let (paramInfo, paramCtx, paramElabs, state1) =
    List.fold_left(
      ((accInfo, accCtx, accElabs, accState), p: param) => {
        let (typeInfo, newState) =
          checkOLTerm(accState, accCtx, Expression(Some(olHole)), p.paramType);
        let elabType =
          switch (typeInfo.elaborated) {
          | Some(e) => e
          | None => p.paramType
          };
        /* Param-shadowing warning + def link: another decl, an earlier
           param, or even the decl's self-binding sharing this name. */
        let (paramShadowWarns, paramShadowDefs) =
          shadowCheck(p.paramName, p.nameMeta, accCtx);
        let typeInfo = withErrors(typeInfo, paramShadowWarns);
        let typeInfo = {
          ...typeInfo,
          definitions: typeInfo.definitions @ paramShadowDefs,
        };
        /* Within the decl's own check, later params see the elaborated
           paramType (which may carry per-decl metas — that's fine, they
           live in the same elaboration state). */
        let newCtx =
          StringMap.add(p.paramName, OL(Some(([], elabType)), Some(p.nameMeta)), accCtx);
        (mergeInfos(accInfo, typeInfo), newCtx, accElabs @ [elabType], newState);
      },
      (emptyInfo, selfCtx, [], emptyElabState),
      d.params,
    );
  let paramInfo = withErrors(paramInfo, selfShadowWarns);
  let paramInfo = {
    ...paramInfo,
    definitions: paramInfo.definitions @ selfShadowDefs,
  };
  /* typeTerm: check retType in Γ[x ā : T][ā] */
  let (retInfo, finalState) =
    checkOLTerm(state1, paramCtx, Expression(Some(olHole)), d.retType);
  let retElab =
    switch (retInfo.elaborated) {
    | Some(e) => e
    | None => d.retType
    };
  let merged = mergeInfos(paramInfo, retInfo);
  let zonked = zonkInlayHints(finalState.solutions, merged);
  let resolved = resolveHoleGoals(finalState.solutions, zonked);
  /* Build the EXTERNAL binding: param types and retType use their
     elaborated forms, fully zonked, with surviving (unsolved) metas
     replaced by synthesized holes — so this decl's local meta IDs
     don't leak into other decls. Holes act as wildcards under
     unification, preserving permissiveness for any unfillable slot. */
  let zonkClean = zonkAndForgetMetas(finalState.solutions);
  let externalParamPairs =
    List.map2(
      (p: param, et) => (Some(p.paramName), zonkClean(et)),
      d.params,
      paramElabs,
    );
  let externalRetType = zonkClean(retElab);
  let externalBinding =
    OL(Some((externalParamPairs, externalRetType)), Some(d.nameMeta));
  let bindings = StringMap.singleton(d.declName, externalBinding);
  /* Warn on incomplete inferred-arg runs. Each term former whose
     elaborator-inserted ghosts didn't all get solved gets a yellow
     squiggle at the head. Pulled from this decl's elabState — every
     insertion site is recorded there at allocation, so the warning
     localization is exact (and doesn't require walking the AST or
     filtering foreign source positions). Warnings — not errors — so
     idempotence on errors still holds: re-elaborating a printed `?`
     allocates a user-hole meta (with ghost=false; the insertion isn't
     recorded in ghostInsertions), which the walker doesn't flag. */
  let ghostWarns = collectGhostWarnings(finalState);
  let coerceWarns = collectCoerceWarnings(finalState);
  let resolved = withErrors(resolved, ghostWarns @ coerceWarns);
  /* Per-decl completeness (type-level only; witness-level is added by
     runConstructSchema for construct decls). A decl is type-complete iff
     no hole survives in its elaborated paramTypes / retType, no semantic
     errors fired during this decl's check, AND every external reference
     resolves to an already-complete decl. */
  let typeHasHoles =
    olHasHoles(externalRetType)
    || List.exists(
         ((_, ty)) => olHasHoles(ty),
         externalParamPairs,
       );
  let typeRefs =
    List.concat(
      List.map(((_, ty)) => olCollectRefs(ty, ctx), externalParamPairs),
    )
    @ olCollectRefs(externalRetType, ctx);
  let hasErrors = Error.hasRealErrors(resolved.errors);
  let typeComplete =
    !typeHasHoles && !hasErrors && allRefsComplete(typeRefs);
  completenessRef := StringMap.add(d.declName, typeComplete, completenessRef^);
  /* Per-decl elaborated reconstruction: same as the external binding,
     but as a `decl` value so `elaborateProgram` can rebuild the source
     program in declaration order (preserving duplicate names, which a
     binding map collapses). */
  let elabParams =
    List.map2(
      (p: param, et) => {...p, paramType: zonkClean(et)},
      d.params,
      paramElabs,
    );
  let elabDecl = {...d, params: elabParams, retType: externalRetType};
  {...resolved, bindings, elaboratedDecls: [elabDecl]};
}

/* Check an OL term (used for declaration types in postulate/construct).
   Returns the info plus the updated elaboration state (solutions map +
   meta counter), threaded through sub-checks. */
and checkOLTerm =
    (state: elabState, ctx: context, mode: checkingMode, t: ol)
    : (staticInfo, elabState) =>
  switch (t.value) {
  | OLIdentifier(v) =>
    let modeErrors = ensureMode(
      ["expression", "spine", "identifier"], mode, t.meta.start, t.meta.end_,
    );
    switch (mode) {
    | Expression(expected) =>
      switch (lookupCtx(ctx, v)) {
      | NotFound =>
        let err = mark("Unbound variable " ++ v, t.meta.start, t.meta.end_);
        let info = {errors: [err, ...modeErrors], pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, elaborated: Some(t), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
        (info, state);
      | Found(Some((params, retType)), defSite)
          when Option.is_some(expected) && List.length(params) > 0 =>
        /* Identifier-with-params used as a value: elaborate as if the
           user had written `(C ? ? … ?)` with one ghost per param.
           Fires for bare `C` AND `(C)` — the latter is parsed as
           OLAp(C, []) by the builder, which goes through the OLAp
           Expression case. The expected=Some condition makes the
           OLAp head's own Expression(None) lookup not elaborate
           (so the OLAp case can still see the head's full param
           list). Walk params left-to-right, allocating each ghost
           with its position's expected type substituted through
           prior ghosts — that's what enables type-level propagation
           later. */
        let (ghosts, env, state2) =
          List.fold_left(
            ((gs, env, accState), (paramName, paramTy)) => {
              let expectedTy = resolve(env, paramTy);
              let (g, ns) = mkMeta(accState, expectedTy, defaultMeta);
              let env' =
                switch (paramName) {
                | Some(n) => StringMap.add(n, g, env)
                | None => env
                };
              (gs @ [g], env', ns);
            },
            ([], emptyEnv, state),
            params,
          );
        /* Record this insertion site so we can warn at the decl boundary
           if any of these ghosts remain unsolved. Anchored at the head
           identifier `t`. */
        let ghostIds =
          List.filter_map(
            (g: ol) =>
              switch (g.value) {
              | OLMeta(id) => Some(id)
              | _ => None
              },
            ghosts,
          );
        let state2 = {
          ...state2,
          ghostInsertions: state2.ghostInsertions @ [(t.meta, ghostIds)],
        };
        let resolvedRet = resolve(env, retType);
        let inferred = Some(([], resolvedRet));
        /* Wrap with parens=true so a nested elaborated `(d ? ?)`
           prints with its own parens and doesn't flatten into the
           surrounding spine on re-parse — load-bearing for
           idempotence when this elaboration sits as an arg. */
        let elaboratedPre: ol = {
          value: OLAp(t, ghosts),
          meta: {...t.meta, parens: true},
        };
        let (subErrors, state3, coerced, coerceHints) =
          subsume(state2, ctx, expected, inferred, Some(elaboratedPre), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(t) => t
          | None => elaboratedPre
          };
        /* Anchor the inlay hint just after the identifier — its source
           range ends right after the last char of the name (whitespace
           inside surrounding parens does NOT extend it, because the
           builder lifts paren-wrapped identifiers to OLAp(_, [])). */
        let anchor = t.meta.end_;
        let hints = [(anchor, ImplicitArgs, ghosts), ...coerceHints];
        let definitions =
          switch (defSite) {
          | Some(dm) when !t.meta.ghost => [(t.meta, dm)]
          | _ => []
          };
        let info = {
          errors: modeErrors @ subErrors,
          holes: [],
          pendingHoleGoals: [],
          inlayHints: hints,
          definitions,
          inferred,
          mlInferred: None,
          elaborated: Some(elaborated),
          elaboratedDecls: [],
          completeBlocks: [],
          bindings: StringMap.empty,
        };
        (info, state3);
      | Found(inferred, defSite) =>
        let (subErrors, state', coerced, coerceHints) =
          subsume(state, ctx, expected, inferred, Some(t), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(c) => c
          | None => t
          };
        let definitions =
          switch (defSite) {
          | Some(dm) when !t.meta.ghost => [(t.meta, dm)]
          | _ => []
          };
        let info = {errors: modeErrors @ subErrors, pendingHoleGoals: [], holes: [], inlayHints: coerceHints, definitions, inferred, mlInferred: None, elaborated: Some(elaborated), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
        (info, state');
      }
    | _ =>
      let info = {errors: modeErrors, pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, elaborated: Some(t), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
      (info, state);
    };

  | OLAp(f, args) =>
    switch (mode) {
    | Spine =>
      let (funInfo, state1) = checkOLTerm(state, ctx, IdentifierMode, f);
      let initCtx = mergeBindings(ctx, funInfo.bindings);
      let (info, _, finalState) =
        List.fold_left(
          ((accInfo, accCtx, accState), arg) => {
            let (argInfo, newState) = checkOLTerm(accState, accCtx, Argument, arg);
            let combined = mergeInfos(accInfo, argInfo);
            (combined, mergeBindings(accCtx, combined.bindings), newState);
          },
          (funInfo, initCtx, state1),
          args,
        );
      ({...info, elaborated: Some(t)}, finalState);

    | Expression(expected) =>
      let (funInfo, state1) = checkOLTerm(state, ctx, Expression(None), f);
      switch (funInfo.inferred) {
      | None => (funInfo, state1)
      | Some((params, retType)) =>
        let paramCount = List.length(params);
        let argCount = List.length(args);
        /* "Too many" stays a hard error. Under-application is NOT an
           error: the missing leading positions become fresh meta
           variables (the same concept as a user `?`), which may be
           solved by surrounding constraints. Whatever remains unsolved
           is printed as `?` in the elaborated source — exactly what
           re-elaborating would produce, hence idempotence. */
        let hardArityErrors =
          paramCount < argCount
            ? [mark("Too many arguments", f.meta.start, f.meta.end_)] : [];
        let nMissing = max(0, paramCount - argCount);
        let totalSlots = nMissing + argCount;
        let (argInfos, elabArgs, finalEnv, state3) =
          List.fold_left(
            ((accInfos, accElabs, env, accState), i) => {
              /* Slots beyond paramCount correspond to over-applied
                 user args — there's no param type to check against, so
                 we type-check them at a wildcard and don't extend the
                 substitution env. They still pass through into
                 elabArgs so the elaborated form preserves what the
                 user wrote (idempotence). */
              let isOverflow = i >= paramCount;
              let expectedTy =
                if (isOverflow) {
                  olHole;
                } else {
                  let (_, paramTy) = List.nth(params, i);
                  resolve(env, paramTy);
                };
              let isGhost = i < nMissing;
              let (arg, argInfo, newState) =
                if (isGhost) {
                  let (g, ns) = mkMeta(accState, expectedTy, defaultMeta);
                  (g, emptyInfo, ns);
                } else {
                  let userArg = List.nth(args, i - nMissing);
                  let (info, ns) =
                    checkOLTerm(accState, ctx, Expression(Some(expectedTy)), userArg);
                  (userArg, info, ns);
                };
              let argElab =
                switch (argInfo.elaborated) {
                | Some(e) => e
                | None => arg
                };
              let env' =
                if (isOverflow) {
                  env;
                } else {
                  let (paramName, _) = List.nth(params, i);
                  switch (paramName) {
                  | Some(name) => StringMap.add(name, argElab, env)
                  | None => env
                  };
                };
              (
                accInfos @ [argInfo],
                accElabs @ [argElab],
                env',
                newState,
              );
            },
            ([], [], emptyEnv, state1),
            List.init(totalSlots, i => i),
          );
        let effectiveArgs = elabArgs;
        /* Record inserted ghosts (if any) so the decl boundary can warn
           if any remain unsolved. Anchored at the head identifier f.
           The ghosts are the first `nMissing` entries of elabArgs. */
        let ghostIds =
          List.filteri((i, _) => i < nMissing, elabArgs)
          |> List.filter_map((g: ol) =>
               switch (g.value) {
               | OLMeta(id) => Some(id)
               | _ => None
               },
             );
        let state3 =
          nMissing > 0
            ? {...state3, ghostInsertions: state3.ghostInsertions @ [(f.meta, ghostIds)]}
            : state3;
        let info = List.fold_left(mergeInfos, funInfo, argInfos);
        let resolvedRet = resolve(finalEnv, retType);
        let inferred = Some(([], resolvedRet));
        let elabHead = switch (funInfo.elaborated) {
          | Some(e) => e
          | None => f
        };
        let elaboratedPre: ol = {...t, value: OLAp(elabHead, elabArgs)};
        let (subErrors, state4, coerced, coerceHints) =
          subsume(state3, ctx, expected, inferred, Some(elaboratedPre), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(c) => c
          | None => elaboratedPre
          };
        /* Collect the ghost-arg run as a deferred inlay-hint entry; the
           ghost terms (containing metas) get zonked at the decl boundary. */
        let hints = extractArgRunHints(f, effectiveArgs);
        let info = {
          ...info,
          inlayHints: info.inlayHints @ hints @ coerceHints,
        };
        let final = withErrors({...info, inferred, elaborated: Some(elaborated)}, hardArityErrors @ subErrors);
        (final, state4);
      };

    | _ =>
      let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
      let (funInfo, state1) = checkOLTerm(state, ctx, Expression(Some(olHole)), f);
      let (argInfos, finalState) =
        List.fold_left(
          ((accInfos, accState), arg) => {
            let (argInfo, newState) =
              checkOLTerm(accState, ctx, Expression(Some(olHole)), arg);
            (accInfos @ [argInfo], newState);
          },
          ([], state1),
          args,
        );
      let info = List.fold_left(mergeInfos, funInfo, argInfos);
      ({...withErrors(info, modeErrors), elaborated: Some(t)}, finalState);
    }

  | OLHole(_) =>
    /* A user `?` and an elaborator-inserted meta are the SAME concept:
       a unification variable. We allocate a fresh meta here and use it
       as the elaborated form. Subsequent type-level propagation (via
       this position's expected type, recorded on the meta) can solve it.
       The original source position is still registered as a user hole
       so the IDE's holes panel shows it. */
    switch (mode) {
    | Expression(expected) =>
      let expectedTy =
        switch (expected) {
        | Some(e) => e
        | None => olHole
        };
      let id = state.nextMetaId;
      let metaTerm: ol = {value: OLMeta(id), meta: t.meta};
      let state1 = {
        ...state,
        metaTypes: IntMap.add(id, expectedTy, state.metaTypes),
        nextMetaId: id + 1,
      };
      let goal =
        switch (expected) {
        | Some(e) => embedOL(zonk(state1.solutions, e))
        | None => mlHole
        };
      let pending =
        switch (expected) {
        | Some(e) => [(t.meta.start, e)]
        | None => []
        };
      let info = {errors: [], pendingHoleGoals: pending, holes: [(t.meta.start, {goal, context: ctx})], inlayHints: [], definitions: [],
                   inferred: Some(([], expectedTy)), mlInferred: None, elaborated: Some(metaTerm), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
      (info, state1);
    | _ =>
      let info = {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
                   pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: Some(fullHole), mlInferred: None, elaborated: Some(t), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
      (info, state);
    }

  | OLMeta(id) =>
    /* A meta in the input AST: already a unification variable in this
       elaboration state. Look up its recorded type for inferred. This
       case is hit only when an already-elaborated term is re-fed through
       checkOLTerm (idempotence path). */
    switch (mode) {
    | Expression(_) =>
      let inferredTy =
        switch (IntMap.find_opt(id, state.metaTypes)) {
        | Some(ty) => ty
        | None => olHole
        };
      let info = {errors: [], pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [],
                   inferred: Some(([], inferredTy)), mlInferred: None, elaborated: Some(t), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
      (info, state);
    | _ =>
      let info = {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
                   pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: Some(fullHole), mlInferred: None, elaborated: Some(t), elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};
      (info, state);
    }
  }


and checkSchema = (ctx: context, body: ml): staticInfo => {
  let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
  checkExpr(mlCtx, schemaType, body);
}

and checkCoerce = (ctx: context, body: ml): staticInfo => {
  let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
  checkExpr(mlCtx, coerceType, body);
}

and checkPat = (ctx: context, ty: mlType, t: pat): (context, staticInfo) =>
  switch (t.value) {
  | PWildcard => (ctx, emptyInfo)

  | PVar(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(ML(existingTy)) =>
      let errs = mlSubsume(existingTy, ty, t.meta.start, t.meta.end_);
      (ctx, withErrors(emptyInfo, errs));
    | _ =>
      (StringMap.add(name, ML(ty), ctx), emptyInfo)
    }

  | PHole => (ctx, emptyInfo)

  | PString(_) =>
    let errs = mlSubsume(MString, ty, t.meta.start, t.meta.end_);
    (ctx, withErrors(emptyInfo, errs));

  | PList(items) =>
    switch (ty) {
    | MList(elemTy) =>
      List.fold_left(
        ((accCtx, accInfo), item) => {
          let (newCtx, itemInfo) = checkPat(accCtx, elemTy, item);
          (newCtx, mergeInfos(accInfo, itemInfo));
        },
        (ctx, emptyInfo),
        items,
      )
    | MTerm =>
      List.fold_left(
        ((accCtx, accInfo), item) => {
          let (newCtx, itemInfo) = checkPat(accCtx, MTerm, item);
          (newCtx, mergeInfos(accInfo, itemInfo));
        },
        (ctx, emptyInfo),
        items,
      )
    | _ =>
      (ctx, withErrors(emptyInfo,
        [mark("List pattern but expected " ++ printType(ty), t.meta.start, t.meta.end_)]))
    }

  | PCons(headPat, tailPat) =>
    let elemTy = switch (ty) { | MList(e) => e | _ => MTerm };
    let listTy = switch (ty) { | MList(_) => ty | _ => MTerm };
    let (headCtx, headInfo) = checkPat(ctx, elemTy, headPat);
    let (tailCtx, tailInfo) = checkPat(headCtx, listTy, tailPat);
    (tailCtx, mergeInfos(headInfo, tailInfo));

  | PTuple(pats) =>
    switch (ty) {
    | MTuple(types) when List.length(types) == List.length(pats) =>
      List.fold_left2(
        ((accCtx, accInfo), p, pty) => {
          let (newCtx, pInfo) = checkPat(accCtx, pty, p);
          (newCtx, mergeInfos(accInfo, pInfo));
        },
        (ctx, emptyInfo),
        pats,
        types,
      )
    | MTerm =>
      List.fold_left(
        ((accCtx, accInfo), p) => {
          let (newCtx, pInfo) = checkPat(accCtx, MTerm, p);
          (newCtx, mergeInfos(accInfo, pInfo));
        },
        (ctx, emptyInfo),
        pats,
      )
    | _ =>
      (ctx, withErrors(emptyInfo,
        [mark("Tuple pattern but expected " ++ printType(ty), t.meta.start, t.meta.end_)]))
    }

  | PAp(headPat, argPats) =>
    /* OL pattern: constructor application */
    if (eqType(ty, MTerm)) {
      checkOLPatAp(ctx, headPat, argPats)
    } else {
      /* Allow OL patterns when type is unknown/any */
      (ctx, withErrors(emptyInfo,
        [mark("Constructor pattern but expected " ++ printType(ty), t.meta.start, t.meta.end_)]))
    }
  }


and checkOLPatAp = (ctx: context, headPat: pat, argPats: list(pat)): (context, staticInfo) => {
  let checkOLSubpat = (ctx: context, p: pat): (context, staticInfo) =>
    switch (p.value) {
    | PVar(name) =>
      switch (StringMap.find_opt(name, ctx)) {
      | Some(_) => (ctx, emptyInfo)
      | None => (StringMap.add(name, ML(MTerm), ctx), emptyInfo)
      }
    | _ => checkPat(ctx, MTerm, p)
    };
  let (ctx1, headInfo) = checkOLSubpat(ctx, headPat);
  List.fold_left(
    ((accCtx, accInfo), argPat) => {
      let (newCtx, argInfo) = checkOLSubpat(accCtx, argPat);
      (newCtx, mergeInfos(accInfo, argInfo));
    },
    (ctx1, headInfo),
    argPats,
  );
}

/* Check a pattern in OL context: already-bound variables are not type-checked */
and checkOLPat = (ctx: context, p: pat): (context, staticInfo) =>
  switch (p.value) {
  | PVar(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(_) => (ctx, emptyInfo)  /* already bound — just a reference */
    | None =>
      if (!hasOLBindings(ctx)) {
        (ctx, emptyInfo)  /* No OL context — treat as OL constructor */
      } else {
        (StringMap.add(name, ML(MTerm), ctx), emptyInfo)  /* bind as pattern variable */
      }
    }
  | PAp(headName, args) =>
    checkOLPatAp(ctx, headName, args)
  | PHole | PWildcard => (ctx, emptyInfo)
  | PList(items) =>
    List.fold_left(
      ((accCtx, accInfo), item) => {
        let (newCtx, itemInfo) = checkOLPat(accCtx, item);
        (newCtx, mergeInfos(accInfo, itemInfo));
      },
      (ctx, emptyInfo),
      items,
    )
  | PTuple(items) =>
    List.fold_left(
      ((accCtx, accInfo), item) => {
        let (newCtx, itemInfo) = checkOLPat(accCtx, item);
        (newCtx, mergeInfos(accInfo, itemInfo));
      },
      (ctx, emptyInfo),
      items,
    )
  | _ => (ctx, emptyInfo)
  }

and inferExpr = (ctx: context, t: ml): staticInfo =>
  switch (t.value) {
  | Identifier(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(ML(ty)) => setMlType(emptyInfo, ty)
    | Some(Builtin(_)) => setMlType(emptyInfo, MTerm) /* builtins are typed at application site */
    | Some(OL(_)) | Some(SchemaBinding(_)) | Some(CoerceBinding(_)) => setMlType(emptyInfo, MTerm)
    | Some(MetaLet(_, ty)) => setMlType(emptyInfo, ty)
    | None =>
      if (!hasOLBindings(ctx)) {
        /* No OL context — identifier is an OL term literal */
        setMlType(emptyInfo, MTerm)
      } else {
        /* OL context exists — identifier should be in scope */
        withErrors(setMlType(emptyInfo, MTerm),
          [mark("Unbound variable " ++ name, t.meta.start, t.meta.end_)])
      }
    }

  | StringLit(_) => setMlType(emptyInfo, MString)

  | Hole(_) =>
    {errors: [], pendingHoleGoals: [], holes: [(t.meta.start, {goal: mlHole, context: ctx})], inlayHints: [], definitions: [],
     inferred: Some(([], olHole)), mlInferred: Some(MTerm), elaborated: None, elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty}

  | Ap({value: Identifier("fst"), _}, [arg]) =>
    let argInfo = inferExpr(ctx, arg);
    let retTy =
      switch (getInferredMlType(argInfo)) {
      | MTuple([a, ..._]) => a
      | _ => MTerm
      };
    setMlType(argInfo, retTy);

  | Ap({value: Identifier("snd"), _}, [arg]) =>
    let argInfo = inferExpr(ctx, arg);
    let retTy =
      switch (getInferredMlType(argInfo)) {
      | MTuple([_, b, ..._]) => b
      | _ => MTerm
      };
    setMlType(argInfo, retTy);

  | Ap({value: Identifier("apply"), _}, [headArg, argsArg]) =>
    /* apply : Term -> List Term -> Term. Builds Ap(head, args) at runtime,
       letting schemas construct variadic-arity applications. */
    let headInfo = checkExpr(ctx, MTerm, headArg);
    let argsInfo = checkExpr(ctx, MList(MTerm), argsArg);
    setMlType(mergeInfos(headInfo, argsInfo), MTerm);

  | Ap({value: Identifier("foldl"), _}, [fArg, initArg, listArg]) =>
    /* Custom typing for foldl: infer init and list types, check f for consistency */
    let initInfo = inferExpr(ctx, initArg);
    let listInfo = inferExpr(ctx, listArg);
    let initTy = getInferredMlType(initInfo);
    let elemTy =
      switch (getInferredMlType(listInfo)) {
      | MList(t) => t
      | _ => MTerm
      };
    /* f should be: initTy -> elemTy -> initTy (curried) */
    let expectedFTy = MArrow(initTy, MArrow(elemTy, initTy));
    let fInfo = checkExpr(ctx, expectedFTy, fArg);
    let info = mergeInfos(fInfo, mergeInfos(initInfo, listInfo));
    setMlType(info, initTy);

  | Ap(f, args) =>
    let fInfo = inferExpr(ctx, f);
    let fTy = getInferredMlType(fInfo);
    let (retTy, argInfo) =
      List.fold_left(
        ((accTy, accInfo), arg) =>
          switch (accTy) {
          | MArrow(paramTy, retTy) =>
            let aInfo = checkExpr(ctx, paramTy, arg);
            (retTy, mergeInfos(accInfo, aInfo));
          | MTerm =>
            /* OL function application — infer args, result is Term */
            let aInfo = inferExpr(ctx, arg);
            (MTerm, mergeInfos(accInfo, aInfo));
          | ty =>
            let errInfo = withErrors(emptyInfo,
              [mark("Cannot apply value of type " ++ printType(ty), f.meta.start, f.meta.end_)]);
            (MTerm, mergeInfos(accInfo, errInfo));
          },
        (fTy, emptyInfo),
        args,
      );
    let info = mergeInfos(fInfo, argInfo);
    setMlType(info, retTy);

  | Fun(pats, body) =>
    switch (pats) {
    | [] => inferExpr(ctx, body)
    | [pat, ...restPats] =>
      let (patCtx, _patInfo) = checkPat(ctx, MTerm, pat);
      let innerBody = switch (restPats) {
        | [] => body
        | _ => mkML(Fun(restPats, body))
        };
      let bodyInfo = inferExpr(patCtx, innerBody);
      let bodyTy = getInferredMlType(bodyInfo);
      /* Only propagate the inferred type, not errors/holes from inside the body —
         the body will be properly checked when the function is checked against
         a concrete expected type via checkExpr. */
      setMlType(emptyInfo, MArrow(MTerm, bodyTy))
    }

  | Let(b, body) =>
    switch (b.annotation) {
    | Some(annotTy) =>
      let exprInfo = checkExpr(ctx, annotTy, b.rhs);
      let newCtx = StringMap.add(b.name, ML(annotTy), ctx);
      let bodyInfo = inferExpr(newCtx, body);
      mergeInfos(exprInfo, bodyInfo);
    | None =>
      let exprInfo = inferExpr(ctx, b.rhs);
      let exprTy = getInferredMlType(exprInfo);
      let newCtx = StringMap.add(b.name, ML(exprTy), ctx);
      let bodyInfo = inferExpr(newCtx, body);
      mergeInfos(exprInfo, bodyInfo);
    }

  | Match(scrut, branches) =>
    let scrutInfo = inferExpr(ctx, scrut);
    let scrutTy = getInferredMlType(scrutInfo);
    switch (branches) {
    | [] =>
      withErrors(mergeInfos(scrutInfo, setMlType(emptyInfo, MTerm)),
        [mark("Empty match", t.meta.start, t.meta.end_)])
    | [(pat, body), ...rest] =>
      let (patCtx, patInfo) = checkPat(ctx, scrutTy, pat);
      let bodyInfo = inferExpr(patCtx, body);
      let bodyTy = getInferredMlType(bodyInfo);
      let restInfo =
        List.fold_left(
          (accInfo, (p, b)) => {
            let (pCtx, pInfo) = checkPat(ctx, scrutTy, p);
            let bInfo = checkExpr(pCtx, bodyTy, b);
            mergeInfos(accInfo, mergeInfos(pInfo, bInfo));
          },
          emptyInfo,
          rest,
        );
      let info = mergeInfos(scrutInfo, mergeInfos(patInfo, mergeInfos(bodyInfo, restInfo)));
      setMlType(info, bodyTy);
    };

  | If(cond, thenBr, elseBr) =>
    let condInfo = checkExpr(ctx, MBool, cond);
    let thenInfo = inferExpr(ctx, thenBr);
    let thenTy = getInferredMlType(thenInfo);
    let elseInfo = checkExpr(ctx, thenTy, elseBr);
    let info = mergeInfos(condInfo, mergeInfos(thenInfo, elseInfo));
    setMlType(info, thenTy);

  | Tuple(items) =>
    let itemInfos = List.map(item => inferExpr(ctx, item), items);
    let itemTys = List.map(getInferredMlType, itemInfos);
    let info = List.fold_left(mergeInfos, emptyInfo, itemInfos);
    setMlType(info, MTuple(itemTys));

  | List([]) => setMlType(emptyInfo, MList(MTerm))
  | List([first, ...rest]) =>
    let firstInfo = inferExpr(ctx, first);
    let elemTy = getInferredMlType(firstInfo);
    let restInfo =
      List.fold_left(
        (accInfo, item) => mergeInfos(accInfo, checkExpr(ctx, elemTy, item)),
        emptyInfo,
        rest,
      );
    let info = mergeInfos(firstInfo, restInfo);
    setMlType(info, MList(elemTy));

  | Cons(head, tail) =>
    let headInfo = inferExpr(ctx, head);
    let tailInfo = inferExpr(ctx, tail);
    let elemTy = getInferredMlType(headInfo);
    let info = mergeInfos(headInfo, tailInfo);
    setMlType(info, MList(elemTy));

  | BinOp(op, left, right) =>
    switch (op) {
    | Neq | Eq =>
      let leftInfo = inferExpr(ctx, left);
      let leftTy = getInferredMlType(leftInfo);
      let rightInfo = checkExpr(ctx, leftTy, right);
      let info = mergeInfos(leftInfo, rightInfo);
      setMlType(info, MBool);
    | And | Or =>
      let leftInfo = checkExpr(ctx, MBool, left);
      let rightInfo = checkExpr(ctx, MBool, right);
      let info = mergeInfos(leftInfo, rightInfo);
      setMlType(info, MBool);
    }

  | Asc(_, _) =>
    withErrors(setMlType(emptyInfo, MTerm),
      [mark("Unexpected ascription", t.meta.start, t.meta.end_)])

  | Shard(_) | BuilderError =>
    withErrors(setMlType(emptyInfo, MTerm),
      [mark("Invalid expression", t.meta.start, t.meta.end_)])
  }

and checkExpr = (ctx: context, expected: mlType, t: ml): staticInfo =>
  switch (t.value) {
  | Hole(_) =>
    let goal = mlTypeToTerm(expected);
    {errors: [], pendingHoleGoals: [], holes: [(t.meta.start, {goal, context: ctx})], inlayHints: [], definitions: [],
     inferred: None, mlInferred: None, elaborated: None, elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty};

  | Fun(pats, body) =>
    switch (pats, expected) {
    | ([pat, ...restPats], MArrow(paramTy, retTy)) =>
      let (patCtx, patInfo) = checkPat(ctx, paramTy, pat);
      let innerBody = switch (restPats) {
        | [] => body
        | _ => mkML(Fun(restPats, body))
        };
      let bodyInfo = checkExpr(patCtx, retTy, innerBody);
      mergeInfos(patInfo, bodyInfo);
    | ([], _) =>
      checkExpr(ctx, expected, body)
    | _ =>
      withErrors(emptyInfo,
        [mark("Lambda but expected " ++ printType(expected), t.meta.start, t.meta.end_)])
    }

  | Match(scrut, branches) =>
    let scrutInfo = inferExpr(ctx, scrut);
    let scrutTy = getInferredMlType(scrutInfo);
    let branchInfo =
      List.fold_left(
        (accInfo, (pat, body)) => {
          let (patCtx, patInfo) = checkPat(ctx, scrutTy, pat);
          let bodyInfo = checkExpr(patCtx, expected, body);
          mergeInfos(accInfo, mergeInfos(patInfo, bodyInfo));
        },
        emptyInfo,
        branches,
      );
    mergeInfos(scrutInfo, branchInfo);

  | If(cond, thenBr, elseBr) =>
    let condInfo = checkExpr(ctx, MBool, cond);
    let thenInfo = checkExpr(ctx, expected, thenBr);
    let elseInfo = checkExpr(ctx, expected, elseBr);
    mergeInfos(condInfo, mergeInfos(thenInfo, elseInfo));

  | Ap({value: Identifier("Ok"), _}, [arg]) =>
    switch (expected) {
    | MResult(innerTy) => checkExpr(ctx, innerTy, arg)
    | _ =>
      withErrors(emptyInfo,
        [mark("Ok but expected " ++ printType(expected), t.meta.start, t.meta.end_)])
    }

  | Ap({value: Identifier("Error"), _}, [arg]) =>
    switch (expected) {
    | MResult(_) => checkExpr(ctx, MString, arg)
    | _ =>
      withErrors(emptyInfo,
        [mark("Error but expected " ++ printType(expected), t.meta.start, t.meta.end_)])
    }

  | List(items) =>
    switch (expected) {
    | MList(elemTy) =>
      List.fold_left(
        (accInfo, item) => mergeInfos(accInfo, checkExpr(ctx, elemTy, item)),
        emptyInfo,
        items,
      )
    | _ =>
      let info = inferExpr(ctx, t);
      let got = getInferredMlType(info);
      withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
    }

  | Let(b, body) =>
    switch (b.annotation) {
    | Some(annotTy) =>
      let exprInfo = checkExpr(ctx, annotTy, b.rhs);
      let newCtx = StringMap.add(b.name, ML(annotTy), ctx);
      let bodyInfo = checkExpr(newCtx, expected, body);
      mergeInfos(exprInfo, bodyInfo);
    | None =>
      let exprInfo = inferExpr(ctx, b.rhs);
      let exprTy = getInferredMlType(exprInfo);
      let newCtx = StringMap.add(b.name, ML(exprTy), ctx);
      let bodyInfo = checkExpr(newCtx, expected, body);
      mergeInfos(exprInfo, bodyInfo);
    }

  | Ap({value: Identifier("foldl"), _}, [fArg, initArg, listArg]) =>
    /* When we know the expected type, use it as initTy so that [] gets
       the right element type instead of defaulting to List Term. */
    let initInfo = checkExpr(ctx, expected, initArg);
    let listInfo = inferExpr(ctx, listArg);
    let elemTy =
      switch (getInferredMlType(listInfo)) {
      | MList(t) => t
      | _ => MTerm
      };
    let expectedFTy = MArrow(expected, MArrow(elemTy, expected));
    let fInfo = checkExpr(ctx, expectedFTy, fArg);
    let info = mergeInfos(fInfo, mergeInfos(initInfo, listInfo));
    setMlType(info, expected);

  | _ =>
    let info = inferExpr(ctx, t);
    let got = getInferredMlType(info);
    withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
  };

/* === Program-level checking on structured blocks === */

let rec checkDeclList = (ctx: context, decls: list(decl)): (staticInfo, context) =>
  List.fold_left(
    ((accInfo, accCtx), d: decl) => {
      let lineInfo = checkDeclLine(accCtx, d);
      let newCtx = mergeBindings(accCtx, lineInfo.bindings);
      (mergeInfos(accInfo, lineInfo), newCtx);
    },
    (emptyInfo, ctx),
    decls,
  )

and processMetaDefs =
    (accInfo: staticInfo, accCtx: context, accDefs: list((string, ml)),
     defs: list(metaDef))
    : (staticInfo, context, list((string, ml))) =>
  switch (defs) {
  | [] => (accInfo, accCtx, accDefs)

  | [SchemaDef(b), ...rest] =>
    let schemaInfo = checkSchema(accCtx, b.rhs);
    let annotErrors =
      switch (b.annotation, b.rawAnnotation) {
      | (Some(ty), _) when !eqType(ty, schemaType) =>
        [mark(
          "Schema type mismatch: annotated "
          ++ printType(ty)
          ++ ", expected "
          ++ printType(schemaType),
          b.bindingMeta.start, b.bindingMeta.end_,
        )]
      | (None, Some(rawExpr)) =>
        [mark("Invalid type annotation", rawExpr.meta.start, rawExpr.meta.end_)]
      | _ => []
      };
    /* The binding has no explicit name meta — derive a name-sized range
       from bindingMeta's start so the warning squiggle and ctrl-click
       hit-area stay tight on the name. */
    let nameMeta = {
      ...b.bindingMeta,
      end_: b.bindingMeta.start + String.length(b.name),
    };
    let (shadowWarns, shadowDefs) = shadowCheck(b.name, nameMeta, accCtx);
    let info =
      withErrors(mergeInfos(accInfo, schemaInfo), annotErrors @ shadowWarns);
    let info = {...info, definitions: info.definitions @ shadowDefs};
    let newCtx = StringMap.add(b.name, SchemaBinding(b.rhs), accCtx);
    processMetaDefs(info, newCtx, accDefs, rest);

  | [CoerceDef(b), ...rest] =>
    let coerceInfo = checkCoerce(accCtx, b.rhs);
    let annotErrors =
      switch (b.annotation, b.rawAnnotation) {
      | (Some(ty), _) when !eqType(ty, coerceType) =>
        [mark(
          "Coerce type mismatch: annotated "
          ++ printType(ty)
          ++ ", expected "
          ++ printType(coerceType),
          b.bindingMeta.start, b.bindingMeta.end_,
        )]
      | (None, Some(rawExpr)) =>
        [mark("Invalid type annotation", rawExpr.meta.start, rawExpr.meta.end_)]
      | _ => []
      };
    let nameMeta = {
      ...b.bindingMeta,
      end_: b.bindingMeta.start + String.length(b.name),
    };
    let (shadowWarns, shadowDefs) = shadowCheck(b.name, nameMeta, accCtx);
    let info =
      withErrors(mergeInfos(accInfo, coerceInfo), annotErrors @ shadowWarns);
    let info = {...info, definitions: info.definitions @ shadowDefs};
    let coerceIdx =
      StringMap.fold(
        (_, binding, acc) =>
          switch (binding) {
          | CoerceBinding(_, _) => acc + 1
          | _ => acc
          },
        accCtx, 0,
      );
    let newCtx = StringMap.add(b.name, CoerceBinding(coerceIdx, b.rhs), accCtx);
    processMetaDefs(info, newCtx, accDefs, rest);

  | [LetDef(b), ...rest] =>
    let (bodyInfo, rhsTy) =
      switch (b.annotation) {
      | Some(ty) => (checkExpr(accCtx, ty, b.rhs), ty)
      | None =>
        let info = inferExpr(accCtx, b.rhs);
        (info, getInferredMlType(info));
      };
    let nameMeta = {
      ...b.bindingMeta,
      end_: b.bindingMeta.start + String.length(b.name),
    };
    let (shadowWarns, shadowDefs) = shadowCheck(b.name, nameMeta, accCtx);
    let bodyInfo = withErrors(bodyInfo, shadowWarns);
    let bodyInfo = {
      ...bodyInfo,
      definitions: bodyInfo.definitions @ shadowDefs,
    };
    let newCtx = StringMap.add(b.name, MetaLet(b.rhs, rhsTy), accCtx);
    let newDefs = accDefs @ [(b.name, b.rhs)];
    processMetaDefs(mergeInfos(accInfo, bodyInfo), newCtx, newDefs, rest);
  };

/* Look up a construct decl's elaborated paramTypes and retType from the
   post-checkDeclList context. Falls back to raw types only if the decl
   wasn't bound (shouldn't happen in normal use). Used by
   runConstructSchema so witnesses are checked against the elaborated
   form — same invariant as if the user had written the implicits
   explicitly. */
let elabDeclTypes =
    (declCtx: context, d: decl): (list((option(string), ol)), ol) =>
  switch (StringMap.find_opt(d.declName, declCtx)) {
  | Some(OL(Some((params, retType)), _)) => (params, retType)
  | _ =>
    let pp = List.map((p: param) => (Some(p.paramName), p.paramType), d.params);
    (pp, d.retType);
  };

let runConstructSchema =
    (ctx: context, declCtx: context, schemaRefName: string,
     schemaMeta: meta, decls: list(decl))
    : list(error) =>
  switch (StringMap.find_opt(schemaRefName, ctx)) {
  | Some(SchemaBinding(schemaBody)) =>
    /* Build eval env from MetaLet definitions in definition order. */
    let rawEnv = List.fold_left(
      (acc, (name, defBody)) =>
        switch (Eval.evalExpr(acc, defBody)) {
        | Eval.Ok(v) => Eval.StringMap.add(name, v, acc)
        | Eval.Err(_) => acc
        },
      Eval.StringMap.empty,
      metaDefsRef^,
    );
    /* Tie the recursive knot: each closure's env-ref is redirected to
       rawEnv so recursive and mutually recursive references resolve. */
    Eval.StringMap.iter(
      (_, v) =>
        switch (v) {
        | Eval.Closure(envRef, _, _) => envRef := rawEnv
        | _ => ()
        },
      rawEnv,
    );
    let evalEnv = rawEnv;
    /* Replace each decl's paramTypes and retType with their elaborated
       forms so the schema sees the same arity/structure that downstream
       type-checking sees. Without this, a user who writes a construct
       decl with implicits (e.g. `eq <Ul l> <Ul l> U1 <Ul lz>` instead
       of the fully-applied 5-arg form) would have their schema pattern
       fail to match because the signature has a different arity than
       the elaborated reality. */
    let elaboratedDecls =
      List.map(
        (d: decl) => {
          let (elabParams, elabRetType) = elabDeclTypes(declCtx, d);
          let elabParamMap =
            List.fold_left(
              (acc, (nameOpt, ty)) =>
                switch (nameOpt) {
                | Some(n) => StringMap.add(n, ty, acc)
                | None => acc
                },
              StringMap.empty,
              elabParams,
            );
          let newParams =
            List.map(
              (p: param) => {
                let elabPty =
                  switch (StringMap.find_opt(p.paramName, elabParamMap)) {
                  | Some(t) => t
                  | None => p.paramType
                  };
                {...p, paramType: elabPty};
              },
              d.params,
            );
          {...d, params: newParams, retType: elabRetType};
        },
        decls,
      );
    switch (Eval.evalExpr(evalEnv, schemaBody)) {
    | Eval.Ok(schemaVal) =>
      let outerSigs = bindingsToSignatures(ctx);
      switch (Eval.runSchema(schemaVal, outerSigs, elaboratedDecls)) {
      | Eval.Witnesses(witnesses) =>
        if (List.length(witnesses) != List.length(elaboratedDecls)) {
          [mark(
            "Schema produced " ++ string_of_int(List.length(witnesses))
            ++ " witnesses but construct has " ++ string_of_int(List.length(elaboratedDecls))
            ++ " declarations",
            schemaMeta.start, schemaMeta.end_,
          )];
        } else {
          let (witnessErrs, witnessHoles, _) = List.fold_left2(
            ((accErrs, accHoles, substEnv), d: decl, witness) => {
              /* d here is from elaboratedDecls — paramTypes and retType
                 are already in their elaborated form. */
              let witnessCtx =
                List.fold_left(
                  (acc, p: param) => {
                    let resolvedPty = resolveWithParams(substEnv, p.paramType);
                    StringMap.add(p.paramName, OL(Some(([], resolvedPty)), Some(p.nameMeta)), acc);
                  },
                  ctx,
                  d.params,
                );
              let expectedType = resolveWithParams(substEnv, d.retType);
              /* Apply [x_j ↦ t_j] substitutions from earlier witnesses to the
                 current witness body too, matching the formalism's
                 [x ↦ t][w̄] where the substitution reaches into both
                 subsequent declarations and subsequent witness terms. */
              let witnessOL = resolveWithParams(substEnv, mlToOL(witness));
              /* Each witness gets a fresh elaboration state — solutions
                 don't cross witness boundaries. */
              let (witnessInfo, witnessState) =
                checkOLTerm(emptyElabState, witnessCtx, Expression(Some(expectedType)), witnessOL);
              let witnessInfo = resolveHoleGoals(witnessState.solutions, witnessInfo);
              /* The "elaborated witness" — what the user-written ML term
                 actually denotes after elaboration: implicits inserted,
                 metas solved. This is what later decls should see when
                 they refer to this name, so omissions in the as-written
                 form (e.g. an under-applied `ap`) don't propagate as
                 arity mismatches into subsequent witness checks. */
              let elabWitnessOL =
                switch (witnessInfo.elaborated) {
                | Some(e) => zonk(witnessState.solutions, e)
                | None => zonk(witnessState.solutions, witnessOL)
                };
              let paramNames = List.map((p: param) => p.paramName, d.params);
              let newSubstEnv =
                StringMap.add(d.declName, (paramNames, embedOL(elabWitnessOL)), substEnv);
              /* Witness contribution to completeness: hole-free witness
                 term, no errors, no registered holes, and every external
                 ref in the witness term is itself complete. AND with the
                 type-level completeness already in the ref. */
              let zonkedWitnessOL = elabWitnessOL;
              let witnessRefs = olCollectRefs(zonkedWitnessOL, ctx);
              let witnessOK =
                !Error.hasRealErrors(witnessInfo.errors)
                && witnessInfo.holes == []
                && !olHasHoles(zonkedWitnessOL)
                && allRefsComplete(witnessRefs);
              let typeComplete =
                switch (StringMap.find_opt(d.declName, completenessRef^)) {
                | Some(b) => b
                | None => false
                };
              completenessRef :=
                StringMap.add(d.declName, typeComplete && witnessOK, completenessRef^);
              (accErrs @ witnessInfo.errors, accHoles @ witnessInfo.holes, newSubstEnv);
            },
            ([], [], emptyWitnessEnv),
            elaboratedDecls,
            witnesses,
          );
          if (List.length(witnessErrs) > 0) {
            let details =
              String.concat("; ", List.map((e: error) => e.message, witnessErrs));
            [mark(
              schemaRefName ++ " matched but generated ill-typed witnesses: " ++ details,
              schemaMeta.start, schemaMeta.end_,
            )];
          } else if (List.length(witnessHoles) > 0) {
              [mark(
              schemaRefName ++ " matched but generated incomplete witnesses",
              schemaMeta.start, schemaMeta.end_,
            )];
          } else {
            [];
          };
        }
      | Eval.SchemaError(msg) =>
        [mark("Schema error: " ++ msg, schemaMeta.start, schemaMeta.end_)]
      }
    | Eval.Err(msg) =>
      [mark("Schema evaluation failed: " ++ msg, schemaMeta.start, schemaMeta.end_)]
    }
  | Some(_) =>
    [mark(schemaRefName ++ " is not a schema", schemaMeta.start, schemaMeta.end_)]
  | None =>
    [mark("Schema " ++ schemaRefName ++ " not found", schemaMeta.start, schemaMeta.end_)]
  };

/* Read each decl's final completeness flag from the ref and emit
   (nameMeta, declMeta) of those marked complete. The bridge does an
   additional filter against syntax errors using declMeta. */
/* True if every decl in `decls` is marked complete in completenessRef
   (no holes, no semantic errors, deps complete). */
let allDeclsComplete = (decls: list(decl)): bool =>
  List.for_all(
    (d: decl) =>
      switch (StringMap.find_opt(d.declName, completenessRef^)) {
      | Some(true) => true
      | _ => false
      },
    decls,
  );

let checkBlock = (ctx: context, block: block): (staticInfo, context) =>
  switch (block) {
  | Postulate(blockMeta, decls) =>
    let (info, finalCtx) = checkDeclList(ctx, decls);
    let completeBlocks =
      allDeclsComplete(decls) ? [blockMeta] : [];
    let info = {...info, completeBlocks: info.completeBlocks @ completeBlocks};
    (withBindings(info, finalCtx), finalCtx);

  | Meta(defs) =>
    let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
    let (metaInfo, metaCtx, metaDefs) =
      processMetaDefs(emptyInfo, mlCtx, [], defs);
    metaDefsRef := metaDefsRef^ @ metaDefs;
    /* mlBuiltins (true, false, fst, snd, foldl, Ok, Error) are valid
       ML names inside this meta block but shouldn't leak into the
       outer context — they would shadow OL constructors a user
       declares with the same name (e.g. `true : bool` in an enum). For
       each builtin key, restore the original ctx binding (or remove if
       unbound originally). */
    let cleanCtx =
      StringMap.fold(
        (k, _v, acc) =>
          switch (StringMap.find_opt(k, ctx)) {
          | Some(orig) => StringMap.add(k, orig, acc)
          | None => StringMap.remove(k, acc)
          },
        mlBuiltins,
        metaCtx,
      );
    (withBindings(metaInfo, cleanCtx), cleanCtx);

  | Construct(schemaName, schemaMeta, blockMeta, decls) =>
    let (bodyInfo, finalCtx) = checkDeclList(ctx, decls);
    let witnessErrors = runConstructSchema(ctx, finalCtx, schemaName, schemaMeta, decls);
    /* If the schema didn't run cleanly (not found, wrong arity, eval
       failure, etc.), every decl in the block fails completeness — the
       per-witness fold may not have even run. */
    if (witnessErrors != []) {
      List.iter(
        (d: decl) =>
          completenessRef := StringMap.add(d.declName, false, completenessRef^),
        decls,
      );
    };
    let info = withErrors(bodyInfo, witnessErrors);
    let completeBlocks =
      allDeclsComplete(decls) ? [blockMeta] : [];
    let info = {...info, completeBlocks: info.completeBlocks @ completeBlocks};
    (withBindings(info, finalCtx), finalCtx);
  };

let checkProgram = (ctx: context, prog: program): staticInfo => {
  /* Reset per-program state. */
  completenessRef := StringMap.empty;
  metaDefsRef := [];
  let (info, _) =
    List.fold_left(
      ((accInfo, accCtx), block) => {
        let (blockInfo, newCtx) = checkBlock(accCtx, block);
        (mergeInfos(accInfo, blockInfo), newCtx);
      },
      (emptyInfo, ctx),
      prog,
    );
  info;
};

/* elaborate : Program → (Program, errors)
   Top-level entry that runs the checker and re-emits the program with
   each decl's elaborated paramTypes/retType substituted in. Idempotent
   in the term-and-errors sense:
     let (p2, e2) = elaborate(p1);
     let (p3, e3) = elaborate(p2);
     => p3 == p2 && e3 == e2
   Achieved structurally: every `?` allocates a unification variable
   that may get solved by surrounding constraints; unsolved variables
   round-trip as `?`, solved ones round-trip as their solved value.
   Per-decl elaborated forms are read positionally from
   `info.elaboratedDecls` so duplicate decl names keep their distinct
   elaborations (a name-keyed lookup would collapse them). */
let elaborateProgram =
    (ctx: context, prog: program): (program, list(error)) => {
  let info = checkProgram(ctx, prog);
  let pool = ref(info.elaboratedDecls);
  let take = () =>
    switch (pool^) {
    | [d, ...rest] =>
      pool := rest;
      Some(d);
    | [] => None
    };
  let elabDecls =
    List.map(d =>
      switch (take()) {
      | Some(ed) => ed
      | None => d
      },
    );
  let elabBlocks =
    List.map(
      block =>
        switch (block) {
        | Postulate(m, decls) => Postulate(m, elabDecls(decls))
        | Meta(_) => block
        | Construct(name, sm, bm, decls) =>
          Construct(name, sm, bm, elabDecls(decls))
        },
      prog,
    );
  (elabBlocks, info.errors);
};
