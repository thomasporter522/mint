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

/* Inlay-hint kinds — the same labels as `ghostKind` from Term.re,
   redeclared as a hint variant for the consumer side. Inlay hints are
   not stored during elaboration; they are derived from the final
   elaborated term by walking its ghost markers. */
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
};

let emptyElabState: elabState = {
  solutions: IntMap.empty,
  metaTypes: IntMap.empty,
  nextMetaId: 0,
};

/* Allocate a fresh meta as an Implicit-ghost subterm at the given
   source meta, recording the expected type for type-level propagation.
   Every call site for mkMeta is the elaborator filling in an arg the
   user under-applied — so the kind is always Implicit. Coerce-kind
   ghosts come from substituteAndGhost, which wraps procedure outputs. */
let mkMeta = (state: elabState, expectedTy: ol, m: meta): (ol, elabState) => {
  let id = state.nextMetaId;
  let t: ol = {value: OLMeta(id), meta: asGhost(Implicit, m)};
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
  /* `⟐` auto-hole sites: same shape as `holes`, recorded separately so
     the JS bridge can invoke Canonical only for these. After Canonical
     returns a candidate, the source is rewritten and re-elaborated. */
  autoHoles: list((int, holeInfo)),
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
  /* Every parsed block's source range (regardless of completeness).
     The bridge uses this to recompute block-level checkmarks after
     resolving Canonical auto-holes — a block that was incomplete only
     because of an auto-hole becomes complete once Canonical fills it. */
  allBlocks: list(meta),
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

let emptyInfo = {errors: [], pendingHoleGoals: [], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, elaborated: None, elaboratedDecls: [], completeBlocks: [], bindings: StringMap.empty, autoHoles: [], allBlocks: []};

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

/* `⟐` auto-hole sites recorded during the program check: maps the
   source offset of each `⟐` to its (context, expected type) at
   elaboration time.  Read by the externally-exposed
   `verifyAutoCandidateJs` so the bridge can present a candidate to the
   kernel for a focused check (no re-elaboration of the program).
   Reset per `checkProgram`. */
let autoHoleContextsRef: ref(IntMap.t((context, ol))) = ref(IntMap.empty);

/* Tag-introduction namespace. Populated by `meta { newtag #foo }`,
   read by tag-line validation and by `bindingsToSignatures` (which
   queries `tagsByNameRef` per-binding). Reset per `checkProgram`. */
module StringSet = Set.Make(String);
let tagNamespaceRef: ref(StringSet.t) = ref(StringSet.empty);

/* Per-binding tag annotations. Each OL name → list of tag names
   applied via `#tag name` lines. Reset per `checkProgram`. */
let tagsByNameRef: ref(StringMap.t(list(string))) = ref(StringMap.empty);

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
  autoHoles: i1.autoHoles @ i2.autoHoles,
  pendingHoleGoals: i1.pendingHoleGoals @ i2.pendingHoleGoals,
  inlayHints: i1.inlayHints @ i2.inlayHints,
  definitions: i1.definitions @ i2.definitions,
  inferred: None,
  mlInferred: None,
  elaborated: None,
  elaboratedDecls: i1.elaboratedDecls @ i2.elaboratedDecls,
  completeBlocks: i1.completeBlocks @ i2.completeBlocks,
  allBlocks: i1.allBlocks @ i2.allBlocks,
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

/* Print a (zonked) ghost subterm for inlay-hint display. After zonking,
   surviving OLMeta(_) subterms are unsolved metavariables and render as
   "?". OLHole(_) cases (synthesized or user-written holes that ended up
   in a ghost slot) also render as "?" — the user never sees meta IDs. */
let rec printGhost = (t: ol): string => {
  /* Wrap parens-less Ap children so the rendering is unambiguous —
     same reason as printOL's pchild. */
  let pchild = (s: ol): string => {
    switch (s.value) {
    | OLAp(_, _) when !s.meta.parens => "(" ++ printGhost(s) ++ ")"
    | _ => printGhost(s)
    }
  };
  switch (t.value) {
  | OLHole(_) | OLMeta(_) => "?"
  | OLIdentifier(s) => s
  | OLAp(f, args) =>
    let inside =
      pchild(f) ++ " " ++ String.concat(" ", List.map(pchild, args));
    t.meta.parens ? "(" ++ inside ++ ")" : inside;
  };
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
let renderHintLabel = (kind: hintKind): string =>
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
  | MBool => mkML(Identifier("Bool"))
  | MString => mkML(Identifier("String"))
  | MTag => mkML(Identifier("Tag"))
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
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Tag") => Some(MTag)
  | Identifier("Signature") =>
    Some(MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm, MList(MTag)]))
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

/* Signature = (Term, List (Term, Term), Term, List Tag) — name, params,
   return type, attached tags. Matches Eval.declToSignature:
   Tuple([name, List(params), retType, List(tags)]). The tag list is
   read from `tagsByNameRef` for each context entry. */
let signatureType =
  MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm, MList(MTag)]);

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
      ("decompose", Builtin("decompose")),
      ("append", Builtin("append")),
      /* Monomorphic builtins */
      ("true", ML(MBool)),
      ("false", ML(MBool)),
      ("Ok", Builtin("Ok")),
      ("Error", Builtin("Error")),
      /* Canonical solver: takes a context (list of signatures, same
         shape as the outer scope passed to schemas) and an expected
         type, returns a Result Term. The bridge wires the actual
         JS-side invocation; without it the call evaluates to
         Error "canonical not available". */
      ("canonical", Builtin("canonical")),
    ],
  );

/* === Unified checker: OL and ML mutually recursive === */

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
/* Walk an elaborated term and pull out both inlay hints and
   "not fully solved" warnings as a function of the term's ghost
   markers. Each ghost subtree carries its kind directly (Implicit /
   Coerce); there is no side table to consult.

   - Maximal leading runs of Implicit-ghost args inside an Ap collapse
     to one `…` hint anchored at the head's end; if any ghost in the
     run is an unsolved meta we additionally emit a warning at the
     head.
   - A Coerce-ghost subtree contains exactly one non-ghost descendant
     (the user's coerced subject; the `exactly one` is enforced by
     `countSentinel` at insertion time). We render `°` at the subject's
     start with the wrap (subject replaced by `□`) as the tooltip; if
     any meta in the wrap is unsolved we emit a warning at the
     subject. */
let extractDiagnostics =
    (strip: ol => ol, sols: IntMap.t(ol), root: ol)
    : (list((int, hintKind, list(ol))), list(error)) => {
  let hints = ref([]);
  let warns = ref([]);
  let isUnsolvedMeta = (t: ol): bool =>
    switch (zonk(sols, t).value) {
    | OLMeta(_) => true
    | _ => false
    };
  let rec containsUnsolved = (t: ol): bool => {
    let t = follow(sols, t);
    switch (t.value) {
    | OLMeta(_) => true
    | OLAp(f, args) =>
      containsUnsolved(f) || List.exists(containsUnsolved, args)
    | _ => false
    };
  };
  /* Locate the single non-ghost descendant within a Coerce-ghost
     subtree. Returns None only if the subtree was malformed (the
     procedure dropped the subject) — the coerce shouldn't have been
     accepted in that case. */
  let rec findSubject = (t: ol): option(ol) =>
    if (!isGhost(t.meta)) {
      Some(t);
    } else {
      switch (t.value) {
      | OLAp(f, args) =>
        let inHead = findSubject(f);
        if (inHead != None) {
          inHead;
        } else {
          List.fold_left(
            (acc, a) =>
              switch (acc) {
              | Some(_) => acc
              | None => findSubject(a)
              },
            None,
            args,
          );
        }
      | _ => None
      };
    };
  /* For the `°` tooltip we want the wrap shown with the subject
     replaced by the `□` box character. The subject is the same `ol`
     reference findSubject returned; replace by physical equality on
     meta.start/end_ since that's stable across the tree. */
  let boxOL: ol = {
    value: OLIdentifier(boxChar),
    meta: defaultMeta,
  };
  let rec substituteBox = (subjectStart, subjectEnd, t: ol): ol =>
    if (t.meta.start == subjectStart && t.meta.end_ == subjectEnd && !isGhost(t.meta)) {
      boxOL;
    } else {
      switch (t.value) {
      | OLAp(f, args) => {
          ...t,
          value:
            OLAp(
              substituteBox(subjectStart, subjectEnd, f),
              List.map(substituteBox(subjectStart, subjectEnd), args),
            ),
        }
      | _ => t
      };
    };
  let rec walk = (t: ol): unit => {
    /* Coerce-ghost wrap: handle the whole subtree here. Don't recurse
       into the wrap's interior (those ghosts are part of THIS wrap).
       Do recurse into the subject (it may have its own coerces or
       implicits). */
    switch (t.meta.ghost) {
    | Some(Coerce) =>
      switch (findSubject(t)) {
      | None => ()
      | Some(subj) =>
        let tooltip = substituteBox(subj.meta.start, subj.meta.end_, t);
        hints := hints^ @ [(subj.meta.start, Coerce, [strip(zonk(sols, tooltip))])];
        if (containsUnsolved(t)) {
          warns :=
            warns^
            @ [
              Error.warn(
                "Coercion not fully solved",
                subj.meta.start, subj.meta.end_,
              ),
            ];
        };
        walk(subj);
      }
    | _ =>
      switch (t.value) {
      | OLAp(f, args) =>
        /* Find the maximal leading run of Implicit-ghost args. They
           collapse to a single `…` anchored at the head's end. */
        let rec splitLeading = (acc: list(ol), xs: list(ol)): (list(ol), list(ol)) =>
          switch (xs) {
          | [a, ...rest] when a.meta.ghost == Some(Implicit) =>
            splitLeading([a, ...acc], rest)
          | _ => (List.rev(acc), xs)
          };
        let (lead, rest) = splitLeading([], args);
        if (lead != []) {
          hints := hints^ @ [(f.meta.end_, ImplicitArgs, List.map(g => strip(zonk(sols, g)), lead))];
          if (List.exists(isUnsolvedMeta, lead)) {
            warns :=
              warns^
              @ [
                Error.warn(
                  "Implicit arguments not fully solved",
                  f.meta.start, f.meta.end_,
                ),
              ];
          };
        };
        walk(f);
        List.iter(walk, rest);
      | _ => ()
      }
    };
  };
  walk(root);
  (hints^, warns^);
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
        let tagList =
          switch (StringMap.find_opt(name, tagsByNameRef^)) {
          | Some(ts) => List.map(t => mkML(TagLit(t)), ts)
          | None => []
          };
        let sig_ =
          mkML(
            Tuple([
              nameTerm,
              mkML(List(paramTuples)),
              embedOL(retType),
              mkML(List(tagList)),
            ]),
          );
        [sig_, ...acc];
      | _ => acc
      },
    ctx,
    [],
  );

/* Check a single declaration line: (name (p1:T1) ...) : RetType.
   Per-decl elaboration state is created here and threaded through
   every sub-check. Solutions never escape this scope. Inlay hints and
   "not fully solved" warnings are derived at the boundary from the
   elaborated term's ghost markers — no diagnostic accumulators in the
   state. */
let coerceSentinelName = "__coerce_subject__";

/* Substitute the original `contents` term back into the procedure's
   result wherever the sentinel identifier appears, and mark every other
   node (the wrapping) as Coerce-ghost. The resulting tree carries the
   full coerce diagnostic structurally: the wrapping subtree's Coerce-
   ghost flags say "this whole region was synthesized as a coercion;
   render `°` at the non-ghost subject inside me." */
let rec substituteAndGhost = (contents: ol, t: ol): ol =>
  switch (t.value) {
  | OLIdentifier(n) when n == coerceSentinelName => contents
  | OLAp(f, args) =>
    let f' = substituteAndGhost(contents, f);
    let args' = List.map(substituteAndGhost(contents), args);
    {value: OLAp(f', args'), meta: asGhost(Coerce, t.meta)}
  | _ => {...t, meta: asGhost(Coerce, t.meta)}
  };

/* Count occurrences of the sentinel identifier in a procedure's output.
   The coerce contract: the procedure receives the subject as a sentinel-
   tagged value and must embed it exactly once in its result. Zero
   occurrences means the wrapping discarded the user's term (a proof of
   anything, not a coercion); more than one means it duplicated it
   (suspect, and breaks the inlay-hint box rendering). Either case is
   a procedure misuse — we fail the coerce and let the inconsistency
   surface unwrapped. */
let rec countSentinel = (t: ol): int =>
  switch (t.value) {
  | OLIdentifier(n) when n == coerceSentinelName => 1
  | OLAp(f, args) =>
    countSentinel(f)
    + List.fold_left((acc, a) => acc + countSentinel(a), 0, args)
  | _ => 0
  };


let rec subsume =
    (state: elabState,
     ctx: context,
     expected: option(ol),
     inferred: option(fullType),
     subterm: option(ol),
     from, to_)
    : (list(error), elabState, option(ol)) => {
  let inferredOut = Option.map(((_, out)) => out, inferred);
  switch (expected, inferredOut) {
  | (Some(exp), Some(inf)) =>
    let (s, conflict) = unify(state, ctx, exp, inf);
    /* Keep the post-unify state on failure so metas committed before
       the mismatch stay solved. The message reports the top-level
       expected and inferred types — not unify's drilled-down conflict
       subterms — zonked against the final state. */
    switch (conflict) {
    | None => ([], s, None)
    | Some(_) =>
      let coerceCandidates = collectCoerceBindings(ctx);
      let canCoerce =
        switch (subterm) {
        | Some(_) when coerceCandidates != [] => true
        | _ => false
        };
      if (canCoerce) {
        switch (tryCoercions(s, ctx, exp, inf, Option.get(subterm), coerceCandidates)) {
        | Some((newState, coercedTerm)) =>
          ([], newState, Some(coercedTerm))
        | None =>
          ([mark(
             "Inconsistency (expected "
             ++ printOL(zonk(s.solutions, exp))
             ++ ", got "
             ++ printOL(zonk(s.solutions, inf))
             ++ ")",
             from, to_,
           )], s, None)
        };
      } else {
        ([mark(
           "Inconsistency (expected "
           ++ printOL(zonk(s.solutions, exp))
           ++ ", got "
           ++ printOL(zonk(s.solutions, inf))
           ++ ")",
           from, to_,
         )], s, None);
      };
    };
  | _ => ([], state, None)
  };
}

and tryCoercions =
    (state: elabState,
     ctx: context,
     expected: ol,
     found: ol,
     contents: ol,
     candidates: list((int, string, ml)))
    : option((elabState, ol)) =>
  switch (candidates) {
  | [] => None
  | [(_idx, _name, body), ...rest] =>
    let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
    let rawEnv =
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
    /* Mutual recursion: rewire each closure's envRef to point at the
       final, complete env so the body can resolve sibling metalets (and
       itself). */
    Eval.StringMap.iter(
      (_, v) =>
        switch (v) {
        | Eval.Closure(envRef, _, _) => envRef := rawEnv
        | _ => ()
        },
      rawEnv,
    );
    let evalEnv = rawEnv;
    switch (Eval.evalExpr(evalEnv, body)) {
    | Err(_) => tryCoercions(state, ctx, expected, found, contents, rest)
    | Ok(procVal) =>
      let outerSigs = bindingsToSignatures(ctx);
      let zExp = zonk(state.solutions, expected);
      let zFound = zonk(state.solutions, found);
      let zContents = zonk(state.solutions, contents);
      /* Pass a sentinel identifier as `contents` so we can locate the
         user's subterm in the procedure's result. */
      let sentinel: ol = {
        value: OLIdentifier(coerceSentinelName),
        meta: defaultMeta,
      };
      switch (Eval.runCoerce(procVal, outerSigs, zExp, zFound, sentinel)) {
      | CoerceFailed(_msg) =>
        tryCoercions(state, ctx, expected, found, contents, rest);
      | Coerced(mlResult) =>
        /* The procedure must embed the sentinel exactly once. Dropping
           it (proves anything) or duplicating it (breaks the structural
           rendering) is a procedure misuse and counts as the coerce
           failing — fall through to the next candidate. */
        let rawOL = mlToOL(mlResult);
        if (countSentinel(rawOL) != 1) {
          tryCoercions(state, ctx, expected, found, contents, rest);
        } else {
          /* The substituted wrap IS the elaborated term's diagnostic
             record: every wrapping node carries Coerce-ghost in its
             meta; the user's subject sits inside as non-ghost. Inlay
             hints and "not fully solved" warnings are derived from
             this structure by extractDiagnostics at the decl
             boundary — no side bookkeeping needed here. */
          let coercedInner = substituteAndGhost(zContents, rawOL);
          let coerced: ol = {
            ...coercedInner,
            meta: {...coercedInner.meta, parens: true},
          };
          let (info, newState) =
            checkOLTerm(state, ctx, Expression(Some(expected)), coerced);
          if (info.errors == []) {
            let final =
              switch (info.elaborated) {
              | Some(t) => t
              | None => coerced
              };
            Some((newState, final));
          } else {
            tryCoercions(state, ctx, expected, found, contents, rest);
          };
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
  let resolved = resolveHoleGoals(finalState.solutions, merged);
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
  /* Inlay hints and "not fully solved" warnings come from one pure
     walk over the decl's elaborated paramTypes and retType. The ghost
     markers in the term carry the full diagnostic structure — no side
     state to consult. `stripImplicits` compacts each hint's payload
     before rendering by removing args the elaborator can re-infer. */
  let strip = stripImplicits(finalState.solutions, paramCtx);
  let extractFromTerm = (t: ol) =>
    extractDiagnostics(strip, finalState.solutions, t);
  let (paramHints, paramWarns) =
    List.fold_left(
      ((accH, accW), pe) => {
        let (h, w) = extractFromTerm(pe);
        (accH @ h, accW @ w);
      },
      ([], []),
      paramElabs,
    );
  let (retHints, retWarns) = extractFromTerm(retElab);
  let allHints = paramHints @ retHints;
  let allWarns = paramWarns @ retWarns;
  let resolved =
    withErrors({...resolved, inlayHints: resolved.inlayHints @ allHints}, allWarns);
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
        let info = {...emptyInfo, errors: [err, ...modeErrors], elaborated: Some(t)};
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
        let (subErrors, state3, coerced) =
          subsume(state2, ctx, expected, inferred, Some(elaboratedPre), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(t) => t
          | None => elaboratedPre
          };
        let definitions =
          switch (defSite) {
          | Some(dm) when !isGhost(t.meta) => [(t.meta, dm)]
          | _ => []
          };
        let info = {
          errors: modeErrors @ subErrors,
          holes: [],
          autoHoles: [],
          allBlocks: [],
          pendingHoleGoals: [],
          inlayHints: [],
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
        let (subErrors, state', coerced) =
          subsume(state, ctx, expected, inferred, Some(t), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(c) => c
          | None => t
          };
        let definitions =
          switch (defSite) {
          | Some(dm) when !isGhost(t.meta) => [(t.meta, dm)]
          | _ => []
          };
        let info = {...emptyInfo, errors: modeErrors @ subErrors, definitions, inferred, elaborated: Some(elaborated)};
        (info, state');
      }
    | _ =>
      let info = {...emptyInfo, errors: modeErrors, elaborated: Some(t)};
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
        let info = List.fold_left(mergeInfos, funInfo, argInfos);
        let resolvedRet = resolve(finalEnv, retType);
        let inferred = Some(([], resolvedRet));
        let elabHead = switch (funInfo.elaborated) {
          | Some(e) => e
          | None => f
        };
        let elaboratedPre: ol = {...t, value: OLAp(elabHead, elabArgs)};
        let (subErrors, state4, coerced) =
          subsume(state3, ctx, expected, inferred, Some(elaboratedPre), t.meta.start, t.meta.end_);
        let elaborated =
          switch (coerced) {
          | Some(c) => c
          | None => elaboratedPre
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

  | OLHole(hk) =>
    /* A user `?` and an elaborator-inserted meta are the SAME concept:
       a unification variable. We allocate a fresh meta here and use it
       as the elaborated form. Subsequent type-level propagation (via
       this position's expected type, recorded on the meta) can solve it.
       The original source position is still registered as a user hole
       so the IDE's holes panel shows it. `⟐` (Auto) additionally records
       an autoHoles entry so the JS bridge can dispatch to Canonical. */
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
      let autoHoles =
        switch (hk) {
        | Auto =>
          /* Stash the context+expected so the JS bridge can later
             present a candidate term to a focused checkOLTerm via
             `verifyAutoCandidateJs(offset, candidateOL)`. */
          autoHoleContextsRef :=
            IntMap.add(t.meta.start, (ctx, expectedTy), autoHoleContextsRef^);
          [(t.meta.start, {goal, context: ctx})];
        | _ => []
        };
      let info = {...emptyInfo,
                  pendingHoleGoals: pending,
                  holes: [(t.meta.start, {goal, context: ctx})],
                  inferred: Some(([], expectedTy)),
                  elaborated: Some(metaTerm), autoHoles};
      (info, state1);
    | _ =>
      let info = {...emptyInfo,
                  errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
                  inferred: Some(fullHole), elaborated: Some(t)};
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
      let info = {...emptyInfo, inferred: Some(([], inferredTy)), elaborated: Some(t)};
      (info, state);
    | _ =>
      let info = {...emptyInfo,
                  errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
                  inferred: Some(fullHole), elaborated: Some(t)};
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
    /* Constructor patterns: dispatch on scrutinee type.
       - MTerm     → OL constructor pattern (existing checkOLPatAp path).
       - MResult t → recognise Ok/Error: `Ok x` binds x:t, `Error msg`
                     binds msg:MString. The runtime pattern matcher
                     already handles these structurally. */
    switch (ty) {
    | MTerm => checkOLPatAp(ctx, headPat, argPats)
    | MResult(inner) =>
      switch (headPat.value, argPats) {
      | (PVar("Ok"), [argPat]) => checkPat(ctx, inner, argPat)
      | (PVar("Error"), [argPat]) => checkPat(ctx, MString, argPat)
      | _ =>
        (ctx, withErrors(emptyInfo,
          [mark("Result pattern must be `Ok x` or `Error msg`", t.meta.start, t.meta.end_)]))
      }
    | _ =>
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

  | TagLit(name) =>
    /* `#name` must reference an introduced tag. Unknown tag → error;
       still ascribe MTag so downstream checks don't cascade. */
    let errs =
      if (StringSet.mem(name, tagNamespaceRef^)) {
        [];
      } else {
        [mark(
          "Unknown tag #" ++ name ++ " (introduce with `newtag #" ++ name ++ "`)",
          t.meta.start, t.meta.end_,
        )]
      };
    setMlType(withErrors(emptyInfo, errs), MTag);

  | Hole(_) =>
    {...emptyInfo,
     holes: [(t.meta.start, {goal: mlHole, context: ctx})],
     inferred: Some(([], olHole)), mlInferred: Some(MTerm)}

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

  | Ap({value: Identifier("decompose"), _}, [arg]) =>
    /* decompose : Term -> (Term, List Term). Inverse of `apply`: returns
       (head, args) for an Ap, or (term, []) for any atomic OL value.
       Lets a procedure inspect arbitrary terms structurally — needed to
       walk a rule's LHS against a target term without baking specific
       postulate names into the matcher. */
    let argInfo = checkExpr(ctx, MTerm, arg);
    setMlType(argInfo, MTuple([MTerm, MList(MTerm)]));

  | Ap({value: Identifier("canonical"), _}, [ctxArg, goalArg]) =>
    /* canonical : List (Term, List (Term, Term), Term) -> Term ->
       Result Term.  First arg is a context in the same shape as the
       outer-scope signatures schemas receive; second is the goal. */
    let ctxInfo = checkExpr(ctx, MList(signatureType), ctxArg);
    let goalInfo = checkExpr(ctx, MTerm, goalArg);
    setMlType(mergeInfos(ctxInfo, goalInfo), MResult(MTerm));

  | Ap({value: Identifier("append"), _}, [xsArg, ysArg]) =>
    /* append : List a -> List a -> List a. Both arguments must agree
       on element type; we infer the first and check the second. */
    let xsInfo = inferExpr(ctx, xsArg);
    let xsTy = getInferredMlType(xsInfo);
    let ysInfo = checkExpr(ctx, xsTy, ysArg);
    setMlType(mergeInfos(xsInfo, ysInfo), xsTy);

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
    /* Carry through the body's inferred mlType so that callers like
       `inferExpr.Match` see `(Term, Term)` (or whatever the body
       computed) instead of defaulting to `MTerm` after `mergeInfos`
       drops it. Without this, `let x = … in (a, b)` infers `MTerm` and
       a subsequent match arm at the same body type gets type-checked
       at `MTerm`, producing spurious "Expected Term, got (Term, Term)"
       errors. */
    let info =
      switch (b.annotation) {
      | Some(annotTy) =>
        let exprInfo = checkExpr(ctx, annotTy, b.rhs);
        let newCtx = StringMap.add(b.name, ML(annotTy), ctx);
        let bodyInfo = inferExpr(newCtx, body);
        let merged = mergeInfos(exprInfo, bodyInfo);
        {...merged, mlInferred: bodyInfo.mlInferred};
      | None =>
        let exprInfo = inferExpr(ctx, b.rhs);
        let exprTy = getInferredMlType(exprInfo);
        let newCtx = StringMap.add(b.name, ML(exprTy), ctx);
        let bodyInfo = inferExpr(newCtx, body);
        let merged = mergeInfos(exprInfo, bodyInfo);
        {...merged, mlInferred: bodyInfo.mlInferred};
      };
    info;

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
  }

and checkExpr = (ctx: context, expected: mlType, t: ml): staticInfo =>
  switch (t.value) {
  | Hole(_) =>
    let goal = mlTypeToTerm(expected);
    {...emptyInfo, holes: [(t.meta.start, {goal, context: ctx})]};

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
  }

/* Strip redundant arguments from an elaborated term: at each Ap, peel
   off leading args one at a time while the stripped form still re-
   elaborates to the original (i.e., the elaborator can re-infer them
   from the remaining args). Recurse on the surviving args.

   Used by `extractDiagnostics` to compact inlay-hint payloads before
   rendering — implicit-arg ghost runs and coerce tooltips both pass
   through this so the displayed term shows only the irreducible
   structure.

   Special case: the `□` placeholder (the coerce subject in tooltips)
   is opaque. We can't re-elaborate against it directly (it's not in
   scope), so during the strip-check we substitute it with a `?` hole
   and treat the box position as a wildcard in the equality check. */
and stripImplicits = (sols: IntMap.t(ol), ctx: context, t: ol): ol => {
  let rec equalForStrip = (a: ol, b: ol): bool =>
    switch (a.value, b.value) {
    /* The box position is a wildcard — the user's subject sits there,
       and the strip-check elaborates against a hole, which then becomes
       a meta. */
    | (OLIdentifier(s), _) when s == boxChar => true
    | (_, OLIdentifier(s)) when s == boxChar => true
    | (OLIdentifier(s1), OLIdentifier(s2)) => s1 == s2
    | (OLMeta(_), OLMeta(_)) => true
    | (OLHole(_), OLHole(_)) => true
    | (OLAp(f1, as1), OLAp(f2, as2)) =>
      List.length(as1) == List.length(as2)
      && equalForStrip(f1, f2)
      && List.for_all2(equalForStrip, as1, as2)
    | _ => false
    };
  let rec replaceBoxWithHole = (t: ol): ol =>
    switch (t.value) {
    | OLIdentifier(s) when s == boxChar =>
      {...t, value: OLHole(User)}
    | OLAp(f, args) => {
        ...t,
        value: OLAp(replaceBoxWithHole(f), List.map(replaceBoxWithHole, args)),
      }
    | _ => t
    };
  let rec strip = (t: ol): ol =>
    switch (t.value) {
    | OLAp(f, args) =>
      let target = zonk(sols, t);
      let n = List.length(args);
      let tryStrip = (k: int): option(list(ol)) => {
        let kept = List.filteri((i, _) => i >= k, args);
        let strippedAp: ol = {...t, value: OLAp(f, kept)};
        let stripCheck = replaceBoxWithHole(strippedAp);
        let (info, state) =
          checkOLTerm(emptyElabState, ctx, Expression(None), stripCheck);
        if (info.errors != []) {
          None;
        } else {
          switch (info.elaborated) {
          | None => None
          | Some(elab) =>
            let elabZonked = zonk(state.solutions, elab);
            if (equalForStrip(target, elabZonked)) {
              Some(kept);
            } else {
              None;
            };
          };
        };
      };
      let rec findMaxStrip = (k: int, currentKept: list(ol)): list(ol) =>
        if (k > n) {
          currentKept;
        } else {
          switch (tryStrip(k)) {
          | Some(kept) => findMaxStrip(k + 1, kept)
          | None => currentKept
          };
        };
      let strippedArgs = findMaxStrip(1, args);
      let recursed = List.map(strip, strippedArgs);
      {...t, value: OLAp(f, recursed)};
    | _ => t
    };
  strip(t);
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
    : (staticInfo, context, list((string, ml))) => {
  /* Pre-register every annotated LetDef name with its declared type so
     definitions can mutually reference each other regardless of order
     in the block. Closures created at runtime get their envRefs
     rewired to the complete env at schema/coerce entry, so the same
     visibility holds at runtime. The pre-registration is tracked in
     `preReg` so the per-binding shadow check below can suppress
     warnings for self-pointers, while still catching genuine duplicates
     and outer shadows. */
  let preReg =
    List.fold_left(
      (s, d) =>
        switch (d) {
        | LetDef(b) =>
          switch (b.annotation) {
          | Some(_) => StringSet.add(b.name, s)
          | None => s
          }
        | _ => s
        },
      StringSet.empty, defs,
    );
  let accCtx =
    List.fold_left(
      (c, d) =>
        switch (d) {
        | LetDef(b) =>
          switch (b.annotation) {
          | Some(ty) => StringMap.add(b.name, MetaLet(b.rhs, ty), c)
          | None => c
          }
        | _ => c
        },
      accCtx, defs,
    );
  processMetaDefsLoop(accInfo, accCtx, accDefs, preReg, defs);
}

and processMetaDefsLoop =
    (accInfo: staticInfo, accCtx: context, accDefs: list((string, ml)),
     preReg: StringSet.t, defs: list(metaDef))
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
    processMetaDefsLoop(info, newCtx, accDefs, preReg, rest);

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
    processMetaDefsLoop(info, newCtx, accDefs, preReg, rest);

  | [LetDef(b), ...rest] =>
    let (bodyInfo, rhsTy) =
      switch (b.annotation) {
      | Some(ty) =>
        /* Annotated metalets are pre-registered at block entry (so they
           can mutually refer); accCtx already has this name. The
           recCtx-rebind here is a no-op for the pre-registered case but
           keeps the path correct if the pre-pass is bypassed. */
        let recCtx = StringMap.add(b.name, MetaLet(b.rhs, ty), accCtx);
        (checkExpr(recCtx, ty, b.rhs), ty);
      | None =>
        let info = inferExpr(accCtx, b.rhs);
        (info, getInferredMlType(info));
      };
    let nameMeta = {
      ...b.bindingMeta,
      end_: b.bindingMeta.start + String.length(b.name),
    };
    /* If this name was pre-registered (annotated and in the block-wide
       pre-pass), drop it from the ctx we hand to shadowCheck so the
       pre-registration doesn't trigger a self-shadow warning. We also
       remove it from preReg so a subsequent duplicate by the same name
       still triggers a real shadow warning (because by then the first
       binding has been added to accCtx normally). */
    let (ctxForShadow, preReg) =
      if (StringSet.mem(b.name, preReg)) {
        (StringMap.remove(b.name, accCtx), StringSet.remove(b.name, preReg));
      } else {
        (accCtx, preReg);
      };
    let (shadowWarns, shadowDefs) = shadowCheck(b.name, nameMeta, ctxForShadow);
    let bodyInfo = withErrors(bodyInfo, shadowWarns);
    let bodyInfo = {
      ...bodyInfo,
      definitions: bodyInfo.definitions @ shadowDefs,
    };
    let newCtx = StringMap.add(b.name, MetaLet(b.rhs, rhsTy), accCtx);
    let newDefs = accDefs @ [(b.name, b.rhs)];
    processMetaDefsLoop(mergeInfos(accInfo, bodyInfo), newCtx, newDefs, preReg, rest);

  | [NewtagDef(tag, defMeta), ...rest] =>
    /* Register the tag in the global tag namespace. Redeclaration of an
       existing tag is a warning (consistent with binding shadowing). */
    let errs =
      if (StringSet.mem(tag, tagNamespaceRef^)) {
        [Error.warn(
          "Tag #" ++ tag ++ " already declared",
          defMeta.start, defMeta.end_,
        )];
      } else {
        tagNamespaceRef := StringSet.add(tag, tagNamespaceRef^);
        [];
      };
    processMetaDefsLoop(withErrors(accInfo, errs), accCtx, accDefs, preReg, rest);
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

/* Validate each tag-line in a postulate/construct block:
   - tag must be in the tag namespace (newtag'd earlier)
   - target must be an OL binding in the current/outer scope
   On success, append the tag to `tagsByNameRef`. */
let processTagLines = (ctx: context, lines: list(tagLine)): list(error) =>
  List.concat_map(
    (line: tagLine) => {
      let tagOK = StringSet.mem(line.tag, tagNamespaceRef^);
      let targetOK =
        switch (StringMap.find_opt(line.target, ctx)) {
        | Some(OL(_, _)) => true
        | _ => false
        };
      switch (tagOK, targetOK) {
      | (false, _) =>
        [mark(
          "Unknown tag #" ++ line.tag ++ " (introduce with `newtag #" ++ line.tag ++ "`)",
          line.lineMeta.start, line.lineMeta.end_,
        )]
      | (_, false) =>
        [mark(
          "Unknown constructor `" ++ line.target ++ "`",
          line.lineMeta.start, line.lineMeta.end_,
        )]
      | (true, true) =>
        let existing =
          switch (StringMap.find_opt(line.target, tagsByNameRef^)) {
          | Some(ts) => ts
          | None => []
          };
        if (List.mem(line.tag, existing)) {
          [];
        } else {
          tagsByNameRef :=
            StringMap.add(line.target, existing @ [line.tag], tagsByNameRef^);
          [];
        };
      };
    },
    lines,
  );

let checkBlock = (ctx: context, block: block): (staticInfo, context) =>
  switch (block) {
  | Postulate(blockMeta, decls, tagLines) =>
    let (info, finalCtx) = checkDeclList(ctx, decls);
    let tagErrs = processTagLines(finalCtx, tagLines);
    let completeBlocks =
      allDeclsComplete(decls) ? [blockMeta] : [];
    let info = withErrors(info, tagErrs);
    let info = {
      ...info,
      completeBlocks: info.completeBlocks @ completeBlocks,
      allBlocks: info.allBlocks @ [blockMeta],
    };
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

  | Construct(schemaName, schemaMeta, blockMeta, decls, tagLines) =>
    let (bodyInfo, finalCtx) = checkDeclList(ctx, decls);
    let witnessErrors = runConstructSchema(ctx, finalCtx, schemaName, schemaMeta, decls);
    let tagErrs = processTagLines(finalCtx, tagLines);
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
    let info = withErrors(bodyInfo, witnessErrors @ tagErrs);
    let completeBlocks =
      allDeclsComplete(decls) ? [blockMeta] : [];
    let info = {
      ...info,
      completeBlocks: info.completeBlocks @ completeBlocks,
      allBlocks: info.allBlocks @ [blockMeta],
    };
    (withBindings(info, finalCtx), finalCtx);
  };

let checkProgram = (ctx: context, prog: program): staticInfo => {
  /* Reset per-program state. */
  completenessRef := StringMap.empty;
  metaDefsRef := [];
  autoHoleContextsRef := IntMap.empty;
  tagNamespaceRef := StringSet.empty;
  tagsByNameRef := StringMap.empty;
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

/* Focused check of a Canonical-supplied candidate against the saved
   (context, expected) for an auto-hole at `offset`. Runs the kernel's
   checkOLTerm in Expression(Some(expected)) mode with a fresh elabState
   — no global re-elaboration, no source rewriting. Returns the errors
   the candidate produced (empty list = type-checks). */
let verifyAutoCandidate = (offset: int, candidate: ol): list(error) =>
  switch (IntMap.find_opt(offset, autoHoleContextsRef^)) {
  | None =>
    [Error.mark("No auto-hole context recorded at this offset", offset, offset)]
  | Some((ctx, expected)) =>
    let (info, _) =
      checkOLTerm(emptyElabState, ctx, Expression(Some(expected)), candidate);
    info.errors;
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
        | Postulate(m, decls, tagLines) => Postulate(m, elabDecls(decls), tagLines)
        | Meta(_) => block
        | Construct(name, sm, bm, decls, tagLines) =>
          Construct(name, sm, bm, elabDecls(decls), tagLines)
        },
      prog,
    );
  (elabBlocks, info.errors);
};
