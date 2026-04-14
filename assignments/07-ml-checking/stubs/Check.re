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

/* TODO: Implement mlTypeToTerm.
   Convert an mlType to its term representation:
   - MTerm => Identifier("Term")
   - MSort => Identifier("Sort")
   - MBool => Identifier("Bool")
   - MString => Identifier("String")
   - MList(t) => Ap(Identifier("List"), [addParens(mlTypeToTerm(t))])
   - MResult(t) => Ap(Identifier("Result"), [addParens(mlTypeToTerm(t))])
   - MPair(a, b) => Comma(mlTypeToTerm(a), mlTypeToTerm(b)) with parens: true
   - MArrow(a, b) => Arrow(addParens(mlTypeToTerm(a)), addParens(mlTypeToTerm(b))) */
let rec mlTypeToTerm = (_ty: mlType): term =>
  failwith("TODO");

/* TODO: Implement mlInferred.
   Wrap an mlType as Some(([], mlTypeToTerm(ty))). */
let mlInferred = (_ty: mlType): option(fullType) =>
  failwith("TODO");

/* TODO: Implement mlSubsume.
   Compare two ML types for equality using eqType.
   If equal, return [].
   Otherwise, return an error "Expected ..., got ..." using printType. */
let mlSubsume = (_expected: mlType, _got: mlType, _from, _to_): list(error) =>
  failwith("TODO");

/* TODO: Implement termToMlType.
   Parse a term back into an option(mlType):
   - Identifier("Term") => Some(MTerm)
   - Identifier("Sort") => Some(MSort)
   - Identifier("Bool") => Some(MBool)
   - Identifier("String") => Some(MString)
   - Identifier("Signature") => Some(MPair(MTerm, MPair(MList(MPair(MTerm, MTerm)), MTerm)))
   - Ap(Identifier("List"), [arg]) => recursively convert arg, wrap in MList
   - Ap(Identifier("Result"), [arg]) => recursively convert arg, wrap in MResult
   - Arrow(l, r) => recursively convert both, wrap in MArrow
   - Comma(l, r) => recursively convert both, wrap in MPair
   - Anything else => None */
let rec termToMlType = (_t: term): option(mlType) =>
  failwith("TODO");

/* TODO: Implement getInferredMlType.
   Extract ML type from a staticInfo's inferred field.
   If inferred is Some(([], t)), try termToMlType(t); if Some(ty) return ty, else MTerm.
   Otherwise return MTerm. */
let getInferredMlType = (_info: staticInfo): mlType =>
  failwith("TODO");

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

let hasOLBindings = (ctx: context): bool =>
  StringMap.exists((_, v) => switch (v) { | OL(_) => true | ML(_) | Builtin(_) | SchemaBinding(_) | MetaLet(_, _) => false }, ctx);

/* Signature = (Term, List (Term, Term), Term) — name (as OL identifier), params (name as Identifier term, type), return type */
let signatureType = MPair(MTerm, MPair(MList(MPair(MTerm, MTerm)), MTerm));

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

/* ML builtins context — not part of this assignment */
let mlBuiltins: context = StringMap.empty;


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
    /* Meta block processing — not part of this assignment */
    let _ = body;
    let info =
      switch (rest) {
      | Some(r) => checkTerm(ctx, Program, r)
      | None => emptyInfo
      };
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  | Construct(by, body, rest) =>
    /* Construct block processing — not part of this assignment */
    let (bodyInfo, finalCtx) = checkDecls(ctx, body);
    let _ = by;
    let info = withBindings(bodyInfo, finalCtx);
    let info =
      switch (rest) {
      | Some(r) => mergeInfos(info, checkTerm(finalCtx, Program, r))
      | None => info
      };
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

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

/* === ML checker — implement these functions === */

/* TODO: Implement checkSchema.
   Merge ctx with mlBuiltins, then check body against schemaType via checkExpr. */
and checkSchema = (_ctx: context, _body: term): staticInfo =>
  failwith("TODO")

/* TODO: Implement checkPat.
   Check a pattern against an ML type. Return (extended context, staticInfo).
   Cases:
   - Identifier("_"): wildcard, no binding
   - Identifier(name): if already in ctx as ML(existingTy), subsume; otherwise bind as ML(ty)
   - StringLit(_): subsume MString against ty
   - List(items): if ty is MList(elemTy), check each item against elemTy;
     if ty is MTerm, check each against MTerm; otherwise error
   - Cons(headPats, tailPat): extract elemTy from ty, check heads against elemTy, tail against list ty
   - Comma(left, right): if ty is MPair(tyA, tyB), check left against tyA, right against tyB;
     if MTerm, check both as MTerm; otherwise error
   - Ap(_, _) when ty is MTerm: delegate to checkOLPat
   - Hole(_): no-op
   - Anything else: "Invalid pattern" error */
and checkPat = (ctx: context, _ty: mlType, _t: term): (context, staticInfo) =>
  failwith("TODO")

/* TODO: Implement checkOLPat.
   Check an OL-level pattern (when the expected ML type is Term).
   - Identifier(name): if in scope, treat as constructor (no binding);
     if not in scope and no OL bindings exist, treat as OL constructor;
     if not in scope and OL bindings exist, bind as ML(MTerm)
   - Ap(f, args): recurse into f and args
   - Hole(_): no-op
   - Anything else: no-op */
and checkOLPat = (ctx: context, _t: term): (context, staticInfo) =>
  failwith("TODO")

/* TODO: Implement inferExpr.
   Infer the ML type of an expression. Always return staticInfo (never fail).
   The inferred field carries the type as mlInferred(ty).
   Cases:
   - Identifier(name): look up in ctx
     - ML(ty): infer ty
     - Builtin(_), OL(_), SchemaBinding(_): infer MTerm
     - MetaLet(_, ty): infer ty
     - None: if no OL bindings, infer MTerm (OL literal); otherwise "Unbound variable" error
   - StringLit(_): infer MString
   - Hole(_): produce hole info, infer MTerm
   - Ap(Identifier("fst"), [arg]): infer arg, extract first of MPair
   - Ap(Identifier("snd"), [arg]): infer arg, extract second of MPair
   - Ap(Identifier("foldl"), [f, init, list]): custom typing — infer init and list,
     check f against initTy -> elemTy -> initTy, result is initTy
   - Ap(f, args): infer f, fold over args walking the arrow type;
     MTerm means OL application (infer args); non-arrow non-MTerm is error
   - Asc(expr, _): infer expr
   - Arrow(_, _): infer MSort
   - Eq(_, body): infer body
   - Fun(pat, body): check pat as MTerm, infer body, result is MArrow(MTerm, bodyTy)
   - Let(binding, body): process binding (with optional type annotation), infer body
   - Match(scrut, branches): infer scrutinee, infer first branch for result type,
     check remaining branches against that type
   - If(cond, then, else): check cond as MBool, infer then, check else against thenTy
   - Comma(l, r): infer both, result is MPair
   - List([]): MList(MTerm); List([first, ...rest]): infer first, check rest, MList(elemTy)
   - Cons(heads, tail): infer, result is MList(elemTy)
   - BinOp: ==,!= => MBool; &&,|| => check both MBool, MBool; others => MTerm
   - Shard, BuilderError: "Invalid expression" error, infer MTerm
   - Postulate, Meta, Construct: infer MTerm */
and inferExpr = (_ctx: context, _t: term): staticInfo =>
  failwith("TODO")

/* TODO: Implement checkExpr.
   Check an expression against an expected ML type. Always return staticInfo.
   Cases:
   - Hole(_): produce hole info with expected type as goal
   - Fun(pat, body): if expected is MArrow(paramTy, retTy), check pat and body;
     otherwise "Lambda but expected ..." error
   - Match(scrut, branches): infer scrutinee, check all branch bodies against expected
   - If(cond, then, else): check condition as MBool, check then and else against expected
   - Ap(Identifier("Ok"), [arg]): if expected is MResult(innerTy), check arg against innerTy
   - Ap(Identifier("Error"), [arg]): if expected is MResult(_), check arg against MString
   - List(items): if expected is MList(elemTy), check items; otherwise infer and subsume
   - Let(binding, body): process binding, check body against expected
   - Ap(Identifier("foldl"), [f, init, list]): use expected as initTy for accumulator type
   - Fallthrough: infer and subsume against expected */
and checkExpr = (_ctx: context, _expected: mlType, _t: term): staticInfo =>
  failwith("TODO");

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
