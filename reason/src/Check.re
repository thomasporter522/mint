open Term;
open Print;
open Error;
open MLType;

module StringMap = Map.Make(String);
module IntMap = Map.Make(Int);

/* === Elaboration state (per-declaration) ===
   Underapplied OL constructors are elaborated by inserting metavariables
   for the missing leading arguments. Metas are solved by unification
   whenever two types are compared. Solutions are threaded through the
   check functionally (no refs); each top-level entry into OL checking
   (each decl, each schema-generated witness) gets a fresh state. */

type elabState = {
  solutions: IntMap.t(ol),
  nextMetaId: int,
};

let emptyElabState: elabState = {
  solutions: IntMap.empty,
  nextMetaId: 0,
};

/* Allocate a fresh meta as a ghost subterm at the given source meta. */
let mkMeta = (state: elabState, m: meta): (ol, elabState) => {
  let id = state.nextMetaId;
  let t: ol = {value: OLMeta(id), meta: {...m, ghost: true}};
  (t, {...state, nextMetaId: id + 1});
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

/* Functional unification. Returns Some(new solutions) on success, None
   on failure. User holes match anything (wildcard, like termConsistent
   used to do). Two unsolved metas are aliased by pointing the higher
   ID at the lower. */
let rec unify = (sols: IntMap.t(ol), a: ol, b: ol): option(IntMap.t(ol)) => {
  let a = follow(sols, a);
  let b = follow(sols, b);
  switch (a.value, b.value) {
  | (OLMeta(idA), OLMeta(idB)) when idA == idB => Some(sols)
  | (OLMeta(idA), OLMeta(idB)) =>
    let (lo, hi) = idA < idB ? (idA, idB) : (idB, idA);
    let aliased: ol = {value: OLMeta(lo), meta: defaultMeta};
    Some(IntMap.add(hi, aliased, sols));
  | (OLMeta(id), _) => Some(IntMap.add(id, b, sols))
  | (_, OLMeta(id)) => Some(IntMap.add(id, a, sols))
  | (OLHole(_), _) | (_, OLHole(_)) => Some(sols)
  | (OLIdentifier(x), OLIdentifier(y)) when x == y => Some(sols)
  | (OLAp(f1, args1), OLAp(f2, args2))
      when List.length(args1) == List.length(args2) =>
    let init = unify(sols, f1, f2);
    List.fold_left2(
      (acc, x, y) =>
        switch (acc) {
        | None => None
        | Some(s) => unify(s, x, y)
        },
      init,
      args1,
      args2,
    );
  | _ => None
  };
};

type fullType = (list((option(string), ol)), ol);

type binding =
  /* OL(typing, defSite) — defSite is the source meta of the declaration
     (or param) that introduced this name; used for go-to-definition. */
  | OL(option(fullType), option(meta))
  | ML(mlType)
  | Builtin(string)        /* polymorphic builtin — name identifies the typing rule */
  | SchemaBinding(ml)      /* unevaluated schema body, stored for Construct to evaluate */
  | MetaLet(ml, mlType);   /* unevaluated let body + inferred type, for schema evaluation */

type context = StringMap.t(binding);

type holeInfo = {
  goal: ml,
  context,
};

type staticInfo = {
  errors: list(error),
  holes: list((int, holeInfo)),
  /* Inlay hints: (offset, ghost terms) — anchored just before `offset`.
     Carried as terms (not rendered strings) so they can be zonked at
     the decl boundary against the local solutions map; the API boundary
     prints them. Adding new kinds of ghost insertions only requires
     marking them with meta.ghost = true. */
  inlayHints: list((int, list(ol))),
  /* Definitions: (use, def) — for each OL identifier reference that
     resolves to an OL binding, the meta of the use and the meta of the
     declaration site. Drives go-to-definition. */
  definitions: list((meta, meta)),
  inferred: option(fullType),
  mlInferred: option(mlType),
  bindings: context,
};

let olHole: ol = mkOL(OLHole(User));
let mlHole: ml = mkML(Hole(Synthesized));
let fullHole: fullType = ([], olHole);

let emptyInfo = {errors: [], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, bindings: StringMap.empty};

/* MetaLet definitions in definition order, for eval env construction.
   Set by Meta block processing, read by Construct block. */
let metaDefsRef: ref(list((string, ml))) = ref([]);

let mergeBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let mergeInfos = (i1: staticInfo, i2: staticInfo): staticInfo => {
  errors: i1.errors @ i2.errors,
  holes: i1.holes @ i2.holes,
  inlayHints: i1.inlayHints @ i2.inlayHints,
  definitions: i1.definitions @ i2.definitions,
  inferred: None,
  mlInferred: None,
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
  | Some(ML(_)) | Some(Builtin(_)) | Some(SchemaBinding(_)) | Some(MetaLet(_, _)) => NotFound
  | None => NotFound
  };

/* --- Error helpers --- */

/* Subsume: type-equality check that may solve metas via unification.
   Returns the (possibly updated) solutions alongside any errors. */
let subsume =
    (sols: IntMap.t(ol),
     expected: option(ol),
     inferred: option(fullType),
     from, to_)
    : (list(error), IntMap.t(ol)) => {
  let tooFewArgs =
    switch (inferred, expected) {
    | (Some(([_, ..._], _)), Some(_)) => [mark("Too few arguments", from, to_)]
    | _ => []
    };
  let inferredOut = Option.map(((_, out)) => out, inferred);
  let (inconsistency, sols') =
    switch (expected, inferredOut) {
    | (Some(exp), Some(inf)) =>
      switch (unify(sols, exp, inf)) {
      | Some(s) => ([], s)
      | None =>
        ([mark(
           "Inconsistency (expected "
           ++ printOL(zonk(sols, exp))
           ++ ", got "
           ++ printOL(zonk(sols, inf))
           ++ ")",
           from, to_,
         )], sols)
      }
    | _ => ([], sols)
    };
  (tooFewArgs @ inconsistency, sols');
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

/* Walk an arg list and emit one entry per maximal run of ghost args,
   anchored at the first non-ghost arg that follows the run. The ghost
   terms are returned as-is so the decl boundary can zonk them with the
   final solutions map; the API boundary then prints. */
let extractArgRunHints = (args: list(ol)): list((int, list(ol))) => {
  let rec go =
          (acc: list((int, list(ol))), run: list(ol), args: list(ol))
          : list((int, list(ol))) =>
    switch (args) {
    | [] => List.rev(acc)
    | [a, ...rest] =>
      if (a.meta.ghost) {
        go(acc, [a, ...run], rest);
      } else if (run != []) {
        go([(a.meta.start, List.rev(run)), ...acc], [], rest);
      } else {
        go(acc, [], rest);
      }
    };
  go([], [], args);
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

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

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
      ((pos, ghosts)) => (pos, List.map(zonk(sols), ghosts)),
      info.inlayHints,
    );
  {...info, inlayHints: zonked};
};

/* Check a single declaration line: (name (p1:T1) ...) : RetType.
   Per-decl elaboration state is created here, threaded through every
   sub-check, and consumed at the end via zonkInlayHints. Solutions
   never escape this scope. */
let rec checkDeclLine = (ctx: context, d: decl): staticInfo => {
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
  let paramPairs =
    List.map((p: param) => (Some(p.paramName), p.paramType), d.params);
  let selfBinding = OL(Some((paramPairs, d.retType)), Some(d.nameMeta));
  let selfCtx = StringMap.add(d.declName, selfBinding, ctx);
  /* typeArgs: check each param's type, threading the elaboration state. */
  let (paramInfo, paramCtx, state1) =
    List.fold_left(
      ((accInfo, accCtx, accState), p: param) => {
        let (typeInfo, newState) =
          checkOLTerm(accState, accCtx, Expression(Some(olHole)), p.paramType);
        let newCtx =
          StringMap.add(p.paramName, OL(Some(([], p.paramType)), Some(p.nameMeta)), accCtx);
        (mergeInfos(accInfo, typeInfo), newCtx, newState);
      },
      (emptyInfo, selfCtx, emptyElabState),
      d.params,
    );
  /* typeTerm: check retType in Γ[x ā : T][ā] */
  let (retInfo, finalState) =
    checkOLTerm(state1, paramCtx, Expression(Some(olHole)), d.retType);
  let merged = mergeInfos(paramInfo, retInfo);
  let zonked = zonkInlayHints(finalState.solutions, merged);
  let bindings = StringMap.singleton(d.declName, selfBinding);
  {...zonked, bindings};
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
        let info = {errors: [err, ...modeErrors], holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
        (info, state);
      | Found(inferred, defSite) =>
        let (subErrors, sols') =
          subsume(state.solutions, expected, inferred, t.meta.start, t.meta.end_);
        let definitions =
          switch (defSite) {
          | Some(dm) when !t.meta.ghost => [(t.meta, dm)]
          | _ => []
          };
        let info = {errors: modeErrors @ subErrors, holes: [], inlayHints: [], definitions, inferred, mlInferred: None, bindings: StringMap.empty};
        (info, {...state, solutions: sols'});
      }
    | _ =>
      let info = {errors: modeErrors, holes: [], inlayHints: [], definitions: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
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
      (info, finalState);

    | Expression(expected) =>
      let (funInfo, state1) = checkOLTerm(state, ctx, Expression(None), f);
      switch (funInfo.inferred) {
      | Some((params, retType)) =>
        let paramCount = List.length(params);
        let argCount = List.length(args);
        let arityErrors =
          checkArity(paramCount, argCount, f.meta.start, f.meta.end_);
        /* Elaborate: when underapplied, prepend a fresh metavariable for
           each missing leading arg. Metas flow through dependent-type
           substitution and may be solved by unification when this
           expression's inferred type meets a more specific expected type. */
        let nMissing = max(0, paramCount - argCount);
        let (leadingGhosts, state2) =
          List.fold_left(
            ((ghosts, accState), _) => {
              let (g, newState) = mkMeta(accState, defaultMeta);
              (ghosts @ [g], newState);
            },
            ([], state1),
            List.init(nMissing, _ => 0),
          );
        let effectiveArgs = leadingGhosts @ args;
        let checkLen = min(paramCount, List.length(effectiveArgs));
        let (argInfos, finalEnv, state3) =
          List.fold_left(
            ((accInfos, env, accState), i) => {
              let (paramName, paramTy) = List.nth(params, i);
              let expectedTy = resolve(env, paramTy);
              let arg = List.nth(effectiveArgs, i);
              let (argInfo, newState) =
                if (arg.meta.ghost) {
                  (emptyInfo, accState);  /* elaboration-inserted; not type-checked */
                } else {
                  checkOLTerm(accState, ctx, Expression(Some(expectedTy)), arg);
                };
              let env =
                switch (paramName) {
                | Some(name) => StringMap.add(name, arg, env)
                | None => env
                };
              (accInfos @ [argInfo], env, newState);
            },
            ([], emptyEnv, state2),
            List.init(checkLen, i => i),
          );
        let info = List.fold_left(mergeInfos, funInfo, argInfos);
        let resolvedRet = resolve(finalEnv, retType);
        let inferred = Some(([], resolvedRet));
        let (subErrors, sols') =
          subsume(state3.solutions, expected, inferred, t.meta.start, t.meta.end_);
        let state4 = {...state3, solutions: sols'};
        /* Collect the ghost-arg run as a deferred inlay-hint entry; the
           ghost terms (containing metas) get zonked at the decl boundary. */
        let hints = extractArgRunHints(effectiveArgs);
        let info = {...info, inlayHints: info.inlayHints @ hints};
        let final = withErrors({...info, inferred}, arityErrors @ subErrors);
        (final, state4);
      | None => (funInfo, state1)
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
      (withErrors(info, modeErrors), finalState);
    }

  | OLHole(_) | OLMeta(_) =>
    /* OLMeta(_) is unreachable from user source (parser doesn't produce
       metas) but the case is kept for exhaustiveness; treat as a hole. */
    switch (mode) {
    | Expression(expected) =>
      let goal =
        switch (expected) {
        | Some(e) => embedOL(zonk(state.solutions, e))
        | None => mlHole
        };
      let info = {errors: [], holes: [(t.meta.start, {goal, context: ctx})], inlayHints: [], definitions: [],
                   inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
      (info, state);
    | _ =>
      let info = {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
                   holes: [], inlayHints: [], definitions: [], inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
      (info, state);
    }
  }


and checkSchema = (ctx: context, body: ml): staticInfo => {
  let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
  checkExpr(mlCtx, schemaType, body);
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
    | Some(OL(_)) | Some(SchemaBinding(_)) => setMlType(emptyInfo, MTerm)
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
    {errors: [], holes: [(t.meta.start, {goal: mlHole, context: ctx})], inlayHints: [], definitions: [],
     inferred: Some(([], olHole)), mlInferred: Some(MTerm), bindings: StringMap.empty}

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
    {errors: [], holes: [(t.meta.start, {goal, context: ctx})], inlayHints: [], definitions: [],
     inferred: None, mlInferred: None, bindings: StringMap.empty};

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
    let info = withErrors(mergeInfos(accInfo, schemaInfo), annotErrors);
    let newCtx = StringMap.add(b.name, SchemaBinding(b.rhs), accCtx);
    processMetaDefs(info, newCtx, accDefs, rest);

  | [LetDef(b), ...rest] =>
    let (bodyInfo, rhsTy) =
      switch (b.annotation) {
      | Some(ty) => (checkExpr(accCtx, ty, b.rhs), ty)
      | None =>
        let info = inferExpr(accCtx, b.rhs);
        (info, getInferredMlType(info));
      };
    let newCtx = StringMap.add(b.name, MetaLet(b.rhs, rhsTy), accCtx);
    let newDefs = accDefs @ [(b.name, b.rhs)];
    processMetaDefs(mergeInfos(accInfo, bodyInfo), newCtx, newDefs, rest);
  };

let runConstructSchema =
    (ctx: context, schemaRefName: string, schemaMeta: meta,
     decls: list(decl))
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
    switch (Eval.evalExpr(evalEnv, schemaBody)) {
    | Eval.Ok(schemaVal) =>
      switch (Eval.runSchema(schemaVal, decls)) {
      | Eval.Witnesses(witnesses) =>
        if (List.length(witnesses) != List.length(decls)) {
          [mark(
            "Schema produced " ++ string_of_int(List.length(witnesses))
            ++ " witnesses but construct has " ++ string_of_int(List.length(decls))
            ++ " declarations",
            schemaMeta.start, schemaMeta.end_,
          )];
        } else {
          let (witnessErrs, witnessHoles, _) = List.fold_left2(
            ((accErrs, accHoles, substEnv), d: decl, witness) => {
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
              let (witnessInfo, _state) =
                checkOLTerm(emptyElabState, witnessCtx, Expression(Some(expectedType)), witnessOL);
              let paramNames = List.map((p: param) => p.paramName, d.params);
              let newSubstEnv =
                StringMap.add(d.declName, (paramNames, witness), substEnv);
              (accErrs @ witnessInfo.errors, accHoles @ witnessInfo.holes, newSubstEnv);
            },
            ([], [], emptyWitnessEnv),
            decls,
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

let checkBlock = (ctx: context, block: block): (staticInfo, context) =>
  switch (block) {
  | Postulate(decls) =>
    let (info, finalCtx) = checkDeclList(ctx, decls);
    (withBindings(info, finalCtx), finalCtx);

  | Meta(defs) =>
    let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
    let (metaInfo, metaCtx, metaDefs) =
      processMetaDefs(emptyInfo, mlCtx, [], defs);
    metaDefsRef := metaDefs;
    (withBindings(metaInfo, metaCtx), metaCtx);

  | Construct(schemaName, decls) =>
    let (bodyInfo, finalCtx) = checkDeclList(ctx, decls);
    let schemaMeta =
      switch (decls) {
      | [d, ..._] => d.declMeta
      | [] => defaultMeta
      };
    let witnessErrors = runConstructSchema(ctx, schemaName, schemaMeta, decls);
    let info = withErrors(bodyInfo, witnessErrors);
    (withBindings(info, finalCtx), finalCtx);
  };

let checkProgram = (ctx: context, prog: program): staticInfo => {
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
