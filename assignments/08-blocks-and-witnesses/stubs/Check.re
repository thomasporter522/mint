open Term;
open Print;
open Error;
open MLType;

module StringMap = Map.Make(String);

type fullType = (list((option(string), term)), term);

type binding =
  | OL(option(fullType))
  | ML(mlType)
  | Builtin(string)        /* polymorphic builtin — name identifies the typing rule */
  | SchemaBinding(term)    /* unevaluated schema body, stored for Construct to evaluate */
  | MetaLet(term, mlType); /* unevaluated let body + inferred type, for schema evaluation */

type context = StringMap.t(binding);

type holeInfo = {
  goal: term,
  context,
};

type staticInfo = {
  errors: list(error),
  holes: list((int, holeInfo)),
  inferred: option(fullType),
  bindings: context,
};

let hole: term = mk(Hole(false));
let fullHole: fullType = ([], hole);

let emptyInfo = {errors: [], holes: [], inferred: None, bindings: StringMap.empty};

/* MetaLet definitions in definition order, for eval env construction.
   Set by Meta block processing, read by Construct block. */
let metaDefsRef: ref(list((string, term))) = ref([]);

let mergeBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let mergeInfos = (i1: staticInfo, i2: staticInfo): staticInfo => {
  errors: i1.errors @ i2.errors,
  holes: i1.holes @ i2.holes,
  inferred: None,
  bindings: mergeBindings(i1.bindings, i2.bindings),
};

let withErrors = (info, errs) => {...info, errors: info.errors @ errs};
let withBindings = (info, ctx) => {...info, bindings: mergeBindings(info.bindings, ctx)};

/* --- Term resolution against an environment --- */

type env = StringMap.t(term);
let emptyEnv: env = StringMap.empty;

/* Witness substitution: maps names to (param_names, witness_body).
   For parameterless decls, param_names is [].
   For (f (x:A)) with witness w, resolving (f arg) gives w[x:=arg]. */
type witnessEnv = StringMap.t((list(string), term));
let emptyWitnessEnv: witnessEnv = StringMap.empty;

let rec resolve = (env: env, t: term): term =>
  if (StringMap.is_empty(env)) {
    t;
  } else {
    switch (t.value) {
    | Identifier(v) =>
      switch (StringMap.find_opt(v, env)) {
      | Some(replacement) => replacement
      | None => t
      }
    | Asc(l, r) =>
      {...t, value: Asc(resolve(env, l), resolve(env, r))}
    | Ap(f, args) =>
      {...t, value: Ap(resolve(env, f), List.map(resolve(env), args))}
    | Postulate(body, rest) =>
      {...t, value: Postulate(List.map(resolve(env), body), Option.map(resolve(env), rest))}
    | Meta(body, rest) =>
      {...t, value: Meta(List.map(resolve(env), body), Option.map(resolve(env), rest))}
    | Construct(by, body, rest) =>
      {...t, value: Construct(resolve(env, by), List.map(resolve(env), body), Option.map(resolve(env), rest))}
    | Arrow(l, r) => {...t, value: Arrow(resolve(env, l), resolve(env, r))}
    | Eq(l, r) => {...t, value: Eq(resolve(env, l), resolve(env, r))}
    | Comma(l, r) => {...t, value: Comma(resolve(env, l), resolve(env, r))}
    | BinOp(op, l, r) => {...t, value: BinOp(op, resolve(env, l), resolve(env, r))}
    | List(items) => {...t, value: List(List.map(resolve(env), items))}
    | Cons(heads, tail) => {...t, value: Cons(List.map(resolve(env), heads), resolve(env, tail))}
    | Fun(pat, body) => {...t, value: Fun(resolve(env, pat), resolve(env, body))}
    | Match(scrut, branches) =>
      {...t, value: Match(resolve(env, scrut), List.map(((p, b)) => (resolve(env, p), resolve(env, b)), branches))}
    | Let(b, body) => {...t, value: Let(resolve(env, b), resolve(env, body))}
    | If(c, th, el) => {...t, value: If(resolve(env, c), resolve(env, th), resolve(env, el))}
    | StringLit(_) | Hole(_) | Shard(_) | BuilderError => t
    };
  }

and resolveWithParams = (wenv: witnessEnv, t: term): term =>
  if (StringMap.is_empty(wenv)) {
    t;
  } else {
    switch (t.value) {
    | Identifier(v) =>
      switch (StringMap.find_opt(v, wenv)) {
      | Some(([], witness)) => witness  /* parameterless: direct substitution */
      | _ => t
      }
    | Ap({value: Identifier(v), _} as f, args) =>
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
          resolve(paramEnv, witness);
        } else {
          {...t, value: Ap(f, resolvedArgs)}
        }
      | _ =>
        {...t, value: Ap(resolveWithParams(wenv, f), List.map(resolveWithParams(wenv), args))}
      }
    | Asc(l, r) =>
      {...t, value: Asc(resolveWithParams(wenv, l), resolveWithParams(wenv, r))}
    | Ap(f, args) =>
      {...t, value: Ap(resolveWithParams(wenv, f), List.map(resolveWithParams(wenv), args))}
    | Arrow(l, r) => {...t, value: Arrow(resolveWithParams(wenv, l), resolveWithParams(wenv, r))}
    | Eq(l, r) => {...t, value: Eq(resolveWithParams(wenv, l), resolveWithParams(wenv, r))}
    | Comma(l, r) => {...t, value: Comma(resolveWithParams(wenv, l), resolveWithParams(wenv, r))}
    | BinOp(op, l, r) => {...t, value: BinOp(op, resolveWithParams(wenv, l), resolveWithParams(wenv, r))}
    | List(items) => {...t, value: List(List.map(resolveWithParams(wenv), items))}
    | Cons(heads, tail) => {...t, value: Cons(List.map(resolveWithParams(wenv), heads), resolveWithParams(wenv, tail))}
    | Fun(pat, body) => {...t, value: Fun(resolveWithParams(wenv, pat), resolveWithParams(wenv, body))}
    | Match(scrut, branches) =>
      {...t, value: Match(resolveWithParams(wenv, scrut),
        List.map(((p, b)) => (resolveWithParams(wenv, p), resolveWithParams(wenv, b)), branches))}
    | Let(b, body) => {...t, value: Let(resolveWithParams(wenv, b), resolveWithParams(wenv, body))}
    | If(c, th, el) => {...t, value: If(resolveWithParams(wenv, c), resolveWithParams(wenv, th), resolveWithParams(wenv, el))}
    | _ => t
    };
  };

/* --- Checking modes --- */

type checkingMode =
  | Program
  | Line
  | Spine
  | Argument
  | IdentifierMode
  | Expression(option(term));

let stringOfMode =
  fun
  | Program => "program"
  | Line => "line"
  | Spine => "spine"
  | Argument => "argument"
  | IdentifierMode => "identifier"
  | Expression(_) => "expression";

/* --- Type consistency --- */

/* Structural consistency: like equality but holes match anything */
let rec termConsistent = (a: term, b: term): bool =>
  switch (a.value, b.value) {
  | (Hole(_), _) | (_, Hole(_)) => true
  | (Identifier(x), Identifier(y)) => x == y
  | (StringLit(x), StringLit(y)) => x == y
  | (Ap(f1, args1), Ap(f2, args2)) =>
    termConsistent(f1, f2)
    && List.length(args1) == List.length(args2)
    && List.for_all2(termConsistent, args1, args2)
  | (List(a), List(b)) =>
    List.length(a) == List.length(b)
    && List.for_all2(termConsistent, a, b)
  | (Cons(h1, t1), Cons(h2, t2)) =>
    List.length(h1) == List.length(h2)
    && List.for_all2(termConsistent, h1, h2)
    && termConsistent(t1, t2)
  | (Comma(a1, b1), Comma(a2, b2)) =>
    termConsistent(a1, a2) && termConsistent(b1, b2)
  | (Arrow(a1, b1), Arrow(a2, b2)) =>
    termConsistent(a1, a2) && termConsistent(b1, b2)
  | (Asc(a1, b1), Asc(a2, b2)) =>
    termConsistent(a1, a2) && termConsistent(b1, b2)
  | _ => false
  };

let consistent = (t1: option(term), t2: option(term)): bool =>
  switch (t1, t2) {
  | (None, _) | (_, None) => true
  | (Some(a), Some(b)) => termConsistent(a, b)
  };

/* --- Context lookup (OL mode) --- */

type lookupResult =
  | Found(option(fullType))
  | NotFound;

let sortTerm = mk(Identifier("Sort"));

let lookupCtx = (ctx: context, x: string): lookupResult =>
  if (x == "Sort") {
    Found(Some(([], sortTerm)));
  } else {
    switch (StringMap.find_opt(x, ctx)) {
    | Some(OL(ft)) => Found(ft)
    | Some(ML(_)) | Some(Builtin(_)) | Some(SchemaBinding(_)) | Some(MetaLet(_, _)) => NotFound
    | None => NotFound
    };
  };

/* --- Error helpers --- */

let subsume =
    (expected: option(term), inferred: option(fullType), from, to_)
    : list(error) => {
  let tooFewArgs =
    switch (inferred) {
    | Some((params, _)) when List.length(params) > 0 && expected != None =>
      [mark("Too few arguments", from, to_)]
    | _ => []
    };
  let inferredOut =
    switch (inferred) {
    | Some((_, out)) => Some(out)
    | None => None
    };
  let inconsistency =
    if (!consistent(expected, inferredOut)) {
      switch (expected, inferredOut) {
      | (Some(exp), Some(inf)) =>
        [mark(
           "Inconsistency (expected "
           ++ printTerm(exp)
           ++ ", got "
           ++ printTerm(inf)
           ++ ")",
           from, to_,
         )]
      | _ => []
      };
    } else {
      [];
    };
  tooFewArgs @ inconsistency;
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

/* --- Extracting params (name + type) from a function signature --- */

let extractParams = (args: list(term)): list((option(string), term)) =>
  List.map(
    (arg: term) =>
      switch (arg.value) {
      | Asc(name, ty) =>
        let paramName =
          switch (name.value) {
          | Identifier(v) => Some(v)
          | _ => None
          };
        (paramName, ty);
      | _ => (None, arg)
      },
    args,
  );

/* === ML type utilities === */

let addParens = (t: term): term =>
  switch (t.value) {
  | Identifier(_) => t
  | _ => {...t, meta: {...t.meta, parens: true}}
  };

let rec mlTypeToTerm =
  fun
  | MTerm => mk(Identifier("Term"))
  | MSort => mk(Identifier("Sort"))
  | MBool => mk(Identifier("Bool"))
  | MString => mk(Identifier("String"))
  | MList(t) => mk(Ap(mk(Identifier("List")), [addParens(mlTypeToTerm(t))]))
  | MResult(t) => mk(Ap(mk(Identifier("Result")), [addParens(mlTypeToTerm(t))]))
  | MPair(a, b) => {
      let t = mk(Comma(mlTypeToTerm(a), mlTypeToTerm(b)));
      {...t, meta: {...t.meta, parens: true}};
    }
  | MArrow(a, b) => mk(Arrow(addParens(mlTypeToTerm(a)), addParens(mlTypeToTerm(b))));

let mlInferred = (ty: mlType): option(fullType) =>
  Some(([], mlTypeToTerm(ty)));

let mlSubsume = (expected: mlType, got: mlType, from, to_): list(error) =>
  if (eqType(expected, got)) {
    [];
  } else {
    [mark(
      "Expected " ++ printType(expected) ++ ", got " ++ printType(got),
      from, to_,
    )];
  };

let rec termToMlType = (t: term): option(mlType) =>
  switch (t.value) {
  | Identifier("Term") => Some(MTerm)
  | Identifier("Sort") => Some(MSort)
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Signature") => Some(MPair(MTerm, MPair(MList(MPair(MTerm, MTerm)), MTerm)))
  | Ap({value: Identifier("List"), _}, [arg]) =>
    switch (termToMlType(arg)) {
    | Some(t) => Some(MList(t))
    | None => None
    }
  | Ap({value: Identifier("Result"), _}, [arg]) =>
    switch (termToMlType(arg)) {
    | Some(t) => Some(MResult(t))
    | None => None
    }
  | Arrow(l, r) =>
    switch (termToMlType(l), termToMlType(r)) {
    | (Some(lt), Some(rt)) => Some(MArrow(lt, rt))
    | _ => None
    }
  | Comma(l, r) =>
    switch (termToMlType(l), termToMlType(r)) {
    | (Some(lt), Some(rt)) => Some(MPair(lt, rt))
    | _ => None
    }
  | _ => None
  };

/* Extract ML type from inferred, defaulting to MTerm */
let getInferredMlType = (info: staticInfo): mlType =>
  switch (info.inferred) {
  | Some(([], t)) =>
    switch (termToMlType(t)) {
    | Some(ty) => ty
    | None => MTerm
    }
  | _ => MTerm
  };

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

let hasOLBindings = (ctx: context): bool =>
  StringMap.exists((_, v) => switch (v) { | OL(_) => true | ML(_) | Builtin(_) | SchemaBinding(_) | MetaLet(_, _) => false }, ctx);

/* Signature = (Term, List (Term, Term), Term) — name (as OL identifier), params (name as Identifier term, type), return type */
let signatureType = MPair(MTerm, MPair(MList(MPair(MTerm, MTerm)), MTerm));

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

/* TODO: ML builtins context — every ML builtin must be declared here.
   Builtins to include:
   - Sort: ML(MTerm) — OL constant available in ML
   - fst, snd, foldl: Builtin("name") — polymorphic, need custom typing rules
   - true, false: ML(MBool)
   - Ok, Error: Builtin("name") — result constructors */
let mlBuiltins: context =
  failwith("TODO: build a StringMap with all ML builtins");


/* === Unified checker: OL and ML mutually recursive === */

let rec checkDecls = (ctx: context, body: list(term)): (staticInfo, context) =>
  List.fold_left(
    ((accInfo, accCtx), line) => {
      let lineInfo = checkTerm(accCtx, Line, line);
      let newCtx = mergeBindings(accCtx, lineInfo.bindings);
      (mergeInfos(accInfo, lineInfo), newCtx);
    },
    (emptyInfo, ctx),
    body,
  )

and checkTerm = (ctx: context, mode: checkingMode, t: term): staticInfo =>
  switch (t.value) {
  | Postulate(body, rest) =>
    let (info, finalCtx) = checkDecls(ctx, body);
    let info = withBindings(info, finalCtx);
    let info =
      switch (rest) {
      | Some(r) => mergeInfos(info, checkTerm(finalCtx, Program, r))
      | None => info
      };
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  | Meta(body, rest) =>
    ignore((body, rest));
    /* TODO: Process the meta block.

       Implement processMeta: a recursive function that scans items and handles:
       1. "schema" keyword followed by Eq(name, rhs) → SchemaBinding
          - Check rhs with checkSchema
          - Handle optional type annotation on name (Asc(Identifier(n), typeAnnot))
          - Verify annotation matches schemaType if present
       2. Eq(Asc(Identifier(n), typeAnnot), rhs) → annotated MetaLet
          - Parse annotation with termToMlType
          - Check rhs against annotation with checkExpr
          - Store as MetaLet(rhs, annotTy)
          - Track in accDefs for definition-order eval env
       3. Eq(Identifier(n), rhs) → bare MetaLet
          - Infer rhs type with inferExpr
          - Store as MetaLet(rhs, rhsTy)
          - Track in accDefs
       4. Unrecognized items → infer and skip

       Then:
       - Merge mlBuiltins into ctx before processing
       - Call processMeta on the body items
       - Store metaDefs in metaDefsRef
       - Check rest with the updated context */
    failwith("TODO: implement Meta block processing");

  | Construct(by, body, rest) =>
    ignore((by, body, rest));
    /* TODO: Process a construct block.

       Steps:
       1. Check declarations with checkDecls (OL scope checking)
       2. Look up the schema name in ctx (must be SchemaBinding)
       3. Build the eval env from metaDefsRef^ in definition order:
          - First pass: evaluate each MetaLet body with the env built so far
          - Second pass: patch all Closure envs to point to the complete env
       4. Evaluate the schema body to get a closure
       5. Call Eval.runSchema to apply it to the declarations
       6. If Witnesses: check count matches, then type-check each witness
          against its declaration's type using resolveWithParams for substitution
       7. If SchemaError: report the error
       8. Add bodyInfo, witnessErrors, finalCtx bindings, check rest */
    failwith("TODO: implement Construct block processing");

  | Identifier(v) =>
    let modeErrors = ensureMode(
      ["expression", "spine", "identifier"], mode, t.meta.start, t.meta.end_,
    );
    switch (mode) {
    | Expression(_) =>
      switch (lookupCtx(ctx, v)) {
      | NotFound =>
        let err = mark("Unbound variable " ++ v, t.meta.start, t.meta.end_);
        {errors: [err, ...modeErrors], holes: [], inferred: None, bindings: StringMap.empty};
      | Found(inferred) =>
        let subErrors =
          switch (mode) {
          | Expression(expected) => subsume(expected, inferred, t.meta.start, t.meta.end_)
          | _ => []
          };
        {errors: modeErrors @ subErrors, holes: [], inferred, bindings: StringMap.empty};
      }
    | _ =>
      {errors: modeErrors, holes: [], inferred: None, bindings: StringMap.empty}
    };

  | Asc(left, right) =>
    switch (mode) {
    | Line =>
      let spineInfo = checkTerm(ctx, Spine, left);
      let bodyCtx = mergeBindings(ctx, spineInfo.bindings);
      let rightInfo = checkTerm(bodyCtx, Expression(Some(hole)), right);
      let info = mergeInfos(spineInfo, rightInfo);
      let bindings =
        switch (left.value) {
        | Identifier(x) =>
          StringMap.singleton(x, OL(Some(([], right))));
        | Ap(f, args) =>
          switch (f.value) {
          | Identifier(x) =>
            StringMap.singleton(x, OL(Some((extractParams(args), right))))
          | _ => StringMap.empty
          }
        | _ => StringMap.empty
        };
      {errors: info.errors, holes: info.holes, inferred: None, bindings};

    | Argument =>
      let leftInfo = checkTerm(ctx, IdentifierMode, left);
      let rightInfo = checkTerm(ctx, Expression(Some(hole)), right);
      let info = mergeInfos(leftInfo, rightInfo);
      if (List.length(leftInfo.errors) == 0) {
        switch (left.value) {
        | Identifier(x) =>
          withBindings(info, StringMap.singleton(x, OL(Some(([], right)))))
        | _ => info
        };
      } else {
        info;
      };

    | _ =>
      let modeErrors = ensureMode(["argument"], mode, t.meta.start, t.meta.end_);
      let info = mergeInfos(
        checkTerm(ctx, Expression(Some(hole)), left),
        checkTerm(ctx, Expression(Some(hole)), right),
      );
      withErrors(info, modeErrors);
    }

  | Ap(f, args) =>
    switch (mode) {
    | Program =>
      let (info, _) =
        List.fold_left(
          ((accInfo, accCtx), item) => {
            let itemInfo = checkTerm(accCtx, Program, item);
            let newCtx = mergeBindings(accCtx, itemInfo.bindings);
            (mergeInfos(accInfo, itemInfo), newCtx);
          },
          (emptyInfo, ctx),
          [f, ...args],
        );
      info;

    | Spine =>
      let (info, _) =
        List.fold_left(
          ((accInfo, accCtx), arg) => {
            let argInfo = checkTerm(accCtx, Argument, arg);
            let combined = mergeInfos(accInfo, argInfo);
            (combined, mergeBindings(accCtx, combined.bindings));
          },
          {
            let funInfo = checkTerm(ctx, IdentifierMode, f);
            (funInfo, mergeBindings(ctx, funInfo.bindings));
          },
          args,
        );
      info;

    | Expression(expected) =>
      let funInfo = checkTerm(ctx, Expression(None), f);
      switch (funInfo.inferred) {
      | Some((params, retType)) =>
        let arityErrors =
          checkArity(List.length(params), List.length(args), f.meta.start, f.meta.end_);
        let minLen = min(List.length(params), List.length(args));
        let (argInfos, finalEnv) =
          List.fold_left(
            ((accInfos, env), i) => {
              let (paramName, paramTy) = List.nth(params, i);
              let expectedTy = resolve(env, paramTy);
              let argInfo = checkTerm(ctx, Expression(Some(expectedTy)), List.nth(args, i));
              let env =
                switch (paramName) {
                | Some(name) => StringMap.add(name, List.nth(args, i), env)
                | None => env
                };
              (accInfos @ [argInfo], env);
            },
            ([], emptyEnv),
            List.init(minLen, i => i),
          );
        let info = List.fold_left(mergeInfos, funInfo, argInfos);
        let retType = resolve(finalEnv, retType);
        let inferred =
          List.length(params) == List.length(args)
            ? Some(([], retType)) : Some(([], hole));
        let subErrors = subsume(expected, inferred, t.meta.start, t.meta.end_);
        withErrors({...info, inferred}, arityErrors @ subErrors);
      | None => funInfo
      };

    | _ =>
      let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
      let funInfo = checkTerm(ctx, Expression(Some(hole)), f);
      let argInfos = List.map(a => checkTerm(ctx, Expression(Some(hole)), a), args);
      withErrors(List.fold_left(mergeInfos, funInfo, argInfos), modeErrors);
    }

  | Hole(_) =>
    switch (mode) {
    | Expression(expected) =>
      let goal =
        switch (expected) {
        | Some(e) => e
        | None => hole
        };
      {errors: [], holes: [(t.meta.start, {goal, context: ctx})],
       inferred: Some(fullHole), bindings: StringMap.empty};
    | _ =>
      {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
       holes: [], inferred: Some(fullHole), bindings: StringMap.empty};
    }

  | Shard(_) =>
    if (t.meta.start >= 0) {
      {errors: [mark("Unexpected token", t.meta.start, t.meta.end_)],
       holes: [], inferred: None, bindings: StringMap.empty};
    } else {
      emptyInfo;
    }

  | BuilderError =>
    if (t.meta.start >= 0) {
      {errors: [mark("Syntax error", t.meta.start, t.meta.end_)],
       holes: [], inferred: None, bindings: StringMap.empty};
    } else {
      emptyInfo;
    }

  | _ => emptyInfo
  }

/* === ML checker — total error localization (mutually recursive with checkTerm) === */
/* inferExpr and checkExpr always return staticInfo, never fail.
   Errors are accumulated. inferExpr sets inferred to carry the ML type. */

and checkSchema = (ctx: context, body: term): staticInfo => {
  let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
  checkExpr(mlCtx, schemaType, body);
}

and checkPat = (ctx: context, ty: mlType, t: term): (context, staticInfo) =>
  switch (t.value) {
  | Identifier("_") => (ctx, emptyInfo)

  | Identifier(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(ML(existingTy)) =>
      let errs = mlSubsume(existingTy, ty, t.meta.start, t.meta.end_);
      (ctx, withErrors(emptyInfo, errs));
    | _ =>
      (StringMap.add(name, ML(ty), ctx), emptyInfo)
    }

  | StringLit(_) =>
    let errs = mlSubsume(MString, ty, t.meta.start, t.meta.end_);
    (ctx, withErrors(emptyInfo, errs));

  | List(items) =>
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

  | Cons(headPats, tailPat) =>
    let elemTy = switch (ty) { | MList(e) => e | _ => MTerm };
    let listTy = switch (ty) { | MList(_) => ty | _ => MTerm };
    let (headCtx, headInfo) = List.fold_left(
      ((accCtx, accInfo), pat) => {
        let (newCtx, patInfo) = checkPat(accCtx, elemTy, pat);
        (newCtx, mergeInfos(accInfo, patInfo));
      },
      (ctx, emptyInfo),
      headPats,
    );
    let (tailCtx, tailInfo) = checkPat(headCtx, listTy, tailPat);
    (tailCtx, mergeInfos(headInfo, tailInfo));

  | Comma(left, right) =>
    switch (ty) {
    | MPair(tyA, tyB) =>
      let (ctx1, info1) = checkPat(ctx, tyA, left);
      let (ctx2, info2) = checkPat(ctx1, tyB, right);
      (ctx2, mergeInfos(info1, info2));
    | MTerm =>
      let (ctx1, info1) = checkPat(ctx, MTerm, left);
      let (ctx2, info2) = checkPat(ctx1, MTerm, right);
      (ctx2, mergeInfos(info1, info2));
    | _ =>
      (ctx, withErrors(emptyInfo,
        [mark("Pair pattern but expected " ++ printType(ty), t.meta.start, t.meta.end_)]))
    }

  | Ap(_, _) when eqType(ty, MTerm) =>
    checkOLPat(ctx, t)

  | Hole(_) => (ctx, emptyInfo)

  | _ =>
    (ctx, withErrors(emptyInfo,
      [mark("Invalid pattern", t.meta.start, t.meta.end_)]))
  }

and checkOLPat = (ctx: context, t: term): (context, staticInfo) =>
  switch (t.value) {
  | Identifier(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(_) => (ctx, emptyInfo)
    | None =>
      if (!hasOLBindings(ctx)) {
        /* No OL context — treat as OL constructor */
        (ctx, emptyInfo)
      } else {
        /* Not in scope — bind as pattern variable */
        (StringMap.add(name, ML(MTerm), ctx), emptyInfo)
      }
    }
  | Ap(f, args) =>
    let (ctx1, fInfo) = checkOLPat(ctx, f);
    List.fold_left(
      ((accCtx, accInfo), arg) => {
        let (newCtx, argInfo) = checkOLPat(accCtx, arg);
        (newCtx, mergeInfos(accInfo, argInfo));
      },
      (ctx1, fInfo),
      args,
    )
  | Hole(_) => (ctx, emptyInfo)
  | _ => (ctx, emptyInfo)
  }

and inferExpr = (ctx: context, t: term): staticInfo =>
  switch (t.value) {
  | Identifier(name) =>
    switch (StringMap.find_opt(name, ctx)) {
    | Some(ML(ty)) => {...emptyInfo, inferred: mlInferred(ty)}
    | Some(Builtin(_)) => {...emptyInfo, inferred: mlInferred(MTerm)} /* builtins are typed at application site */
    | Some(OL(_)) | Some(SchemaBinding(_)) => {...emptyInfo, inferred: mlInferred(MTerm)}
    | Some(MetaLet(_, ty)) => {...emptyInfo, inferred: mlInferred(ty)}
    | None =>
      if (!hasOLBindings(ctx)) {
        /* No OL context — identifier is an OL term literal */
        {...emptyInfo, inferred: mlInferred(MTerm)}
      } else {
        /* OL context exists — identifier should be in scope */
        withErrors({...emptyInfo, inferred: mlInferred(MTerm)},
          [mark("Unbound variable " ++ name, t.meta.start, t.meta.end_)])
      }
    }

  | StringLit(_) => {...emptyInfo, inferred: mlInferred(MString)}

  | Hole(_) =>
    {errors: [], holes: [(t.meta.start, {goal: hole, context: ctx})],
     inferred: mlInferred(MTerm), bindings: StringMap.empty}

  | Ap({value: Identifier("fst"), _}, [arg]) =>
    let argInfo = inferExpr(ctx, arg);
    let retTy =
      switch (getInferredMlType(argInfo)) {
      | MPair(a, _) => a
      | _ => MTerm
      };
    {...argInfo, inferred: mlInferred(retTy)};

  | Ap({value: Identifier("snd"), _}, [arg]) =>
    let argInfo = inferExpr(ctx, arg);
    let retTy =
      switch (getInferredMlType(argInfo)) {
      | MPair(_, b) => b
      | _ => MTerm
      };
    {...argInfo, inferred: mlInferred(retTy)};

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
    {...info, inferred: mlInferred(initTy)};

  | Ap(f, args) =>
    let fInfo = inferExpr(ctx, f);
    let fTy =
      getInferredMlType(fInfo);
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
    {...info, inferred: mlInferred(retTy)};

  | Asc(expr, _typeExpr) =>
    inferExpr(ctx, expr)

  | Arrow(_, _) => {...emptyInfo, inferred: mlInferred(MSort)}

  | Eq(_name, body) => inferExpr(ctx, body)

  | Fun(pat, body) =>
    let (patCtx, _patInfo) = checkPat(ctx, MTerm, pat);
    let bodyInfo = inferExpr(patCtx, body);
    let bodyTy = getInferredMlType(bodyInfo);
    /* Only propagate the inferred type, not errors/holes from inside the body —
       the body will be properly checked when the function is checked against
       a concrete expected type via checkExpr. */
    {...emptyInfo, inferred: mlInferred(MArrow(MTerm, bodyTy))}
  | Let(binding, body) =>
    switch (binding.value) {
    | Eq({value: Asc({value: Identifier(n), _}, typeAnnot), _}, expr) =>
      switch (termToMlType(typeAnnot)) {
      | Some(annotTy) =>
        let exprInfo = checkExpr(ctx, annotTy, expr);
        let newCtx = StringMap.add(n, ML(annotTy), ctx);
        let bodyInfo = inferExpr(newCtx, body);
        mergeInfos(exprInfo, bodyInfo);
      | None =>
        let exprInfo = inferExpr(ctx, expr);
        let exprTy = getInferredMlType(exprInfo);
        let newCtx = StringMap.add(n, ML(exprTy), ctx);
        let bodyInfo = inferExpr(newCtx, body);
        withErrors(mergeInfos(exprInfo, bodyInfo),
          [mark("Invalid type annotation", typeAnnot.meta.start, typeAnnot.meta.end_)]);
      }
    | Eq({value: Identifier(n), _}, expr) =>
      let exprInfo = inferExpr(ctx, expr);
      let exprTy = getInferredMlType(exprInfo);
      let newCtx = StringMap.add(n, ML(exprTy), ctx);
      let bodyInfo = inferExpr(newCtx, body);
      mergeInfos(exprInfo, bodyInfo);
    | _ => inferExpr(ctx, body)
    }

  | Match(scrut, branches) =>
    let scrutInfo = inferExpr(ctx, scrut);
    let scrutTy =
      getInferredMlType(scrutInfo);
    switch (branches) {
    | [] =>
      withErrors(mergeInfos(scrutInfo, {...emptyInfo, inferred: mlInferred(MTerm)}),
        [mark("Empty match", t.meta.start, t.meta.end_)])
    | [(pat, body), ...rest] =>
      let (patCtx, patInfo) = checkPat(ctx, scrutTy, pat);
      let bodyInfo = inferExpr(patCtx, body);
      let bodyTy =
        getInferredMlType(bodyInfo);
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
      {...info, inferred: mlInferred(bodyTy)};
    };

  | If(cond, thenBr, elseBr) =>
    let condInfo = checkExpr(ctx, MBool, cond);
    let thenInfo = inferExpr(ctx, thenBr);
    let thenTy =
      getInferredMlType(thenInfo);
    let elseInfo = checkExpr(ctx, thenTy, elseBr);
    let info = mergeInfos(condInfo, mergeInfos(thenInfo, elseInfo));
    {...info, inferred: mlInferred(thenTy)};

  | Comma(left, right) =>
    let leftInfo = inferExpr(ctx, left);
    let rightInfo = inferExpr(ctx, right);
    let leftTy =
      getInferredMlType(leftInfo);
    let rightTy =
      getInferredMlType(rightInfo);
    let info = mergeInfos(leftInfo, rightInfo);
    {...info, inferred: mlInferred(MPair(leftTy, rightTy))};

  | List([]) => {...emptyInfo, inferred: mlInferred(MList(MTerm))}
  | List([first, ...rest]) =>
    let firstInfo = inferExpr(ctx, first);
    let elemTy =
      getInferredMlType(firstInfo);
    let restInfo =
      List.fold_left(
        (accInfo, item) => mergeInfos(accInfo, checkExpr(ctx, elemTy, item)),
        emptyInfo,
        rest,
      );
    let info = mergeInfos(firstInfo, restInfo);
    {...info, inferred: mlInferred(MList(elemTy))};

  | Postulate(_, _) | Meta(_, _) | Construct(_, _, _) =>
    {...emptyInfo, inferred: mlInferred(MTerm)}

  | Cons(heads, tail) =>
    let headInfos = List.map(h => inferExpr(ctx, h), heads);
    let tailInfo = inferExpr(ctx, tail);
    let info = List.fold_left(mergeInfos, tailInfo, headInfos);
    let elemTy =
      switch (headInfos) {
      | [first, ..._] => getInferredMlType(first)
      | [] => getInferredMlType(tailInfo) |> (fun
        | MList(t) => t
        | _ => MTerm)
      };
    {...info, inferred: mlInferred(MList(elemTy))};

  | BinOp(op, left, right) =>
    switch (op) {
    | "!=" | "==" =>
      let leftInfo = inferExpr(ctx, left);
      let leftTy =
        getInferredMlType(leftInfo);
      let rightInfo = checkExpr(ctx, leftTy, right);
      let info = mergeInfos(leftInfo, rightInfo);
      {...info, inferred: mlInferred(MBool)};
    | "&&" | "||" =>
      let leftInfo = checkExpr(ctx, MBool, left);
      let rightInfo = checkExpr(ctx, MBool, right);
      let info = mergeInfos(leftInfo, rightInfo);
      {...info, inferred: mlInferred(MBool)};
    | _ =>
      let leftInfo = checkExpr(ctx, MTerm, left);
      let rightInfo = checkExpr(ctx, MTerm, right);
      let info = mergeInfos(leftInfo, rightInfo);
      {...info, inferred: mlInferred(MTerm)};
    }

  | Shard(_) | BuilderError =>
    withErrors({...emptyInfo, inferred: mlInferred(MTerm)},
      [mark("Invalid expression", t.meta.start, t.meta.end_)])
  }

and checkExpr = (ctx: context, expected: mlType, t: term): staticInfo =>
  switch (t.value) {
  | Hole(_) =>
    let goal = mlTypeToTerm(expected);
    {errors: [], holes: [(t.meta.start, {goal, context: ctx})],
     inferred: None, bindings: StringMap.empty};

  | Fun(pat, body) =>
    switch (expected) {
    | MArrow(paramTy, retTy) =>
      let (patCtx, patInfo) = checkPat(ctx, paramTy, pat);
      let bodyInfo = checkExpr(patCtx, retTy, body);
      mergeInfos(patInfo, bodyInfo);
    | _ =>
      withErrors(emptyInfo,
        [mark("Lambda but expected " ++ printType(expected), t.meta.start, t.meta.end_)])
    }

  | Match(scrut, branches) =>
    let scrutInfo = inferExpr(ctx, scrut);
    let scrutTy =
      getInferredMlType(scrutInfo);
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
      let got =
        getInferredMlType(info);
      withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
    }

  | Let(binding, body) =>
    switch (binding.value) {
    | Eq({value: Asc({value: Identifier(n), _}, typeAnnot), _}, expr) =>
      switch (termToMlType(typeAnnot)) {
      | Some(annotTy) =>
        let exprInfo = checkExpr(ctx, annotTy, expr);
        let newCtx = StringMap.add(n, ML(annotTy), ctx);
        let bodyInfo = checkExpr(newCtx, expected, body);
        mergeInfos(exprInfo, bodyInfo);
      | None =>
        let exprInfo = inferExpr(ctx, expr);
        let exprTy = getInferredMlType(exprInfo);
        let newCtx = StringMap.add(n, ML(exprTy), ctx);
        let bodyInfo = checkExpr(newCtx, expected, body);
        withErrors(mergeInfos(exprInfo, bodyInfo),
          [mark("Invalid type annotation", typeAnnot.meta.start, typeAnnot.meta.end_)]);
      }
    | Eq({value: Identifier(n), _}, expr) =>
      let exprInfo = inferExpr(ctx, expr);
      let exprTy = getInferredMlType(exprInfo);
      let newCtx = StringMap.add(n, ML(exprTy), ctx);
      let bodyInfo = checkExpr(newCtx, expected, body);
      mergeInfos(exprInfo, bodyInfo);
    | _ => checkExpr(ctx, expected, body)
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
    {...info, inferred: mlInferred(expected)};

  | _ =>
    let info = inferExpr(ctx, t);
    let got =
      getInferredMlType(info);
    withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
  };

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
