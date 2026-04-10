open Term;
open Print;
open Error;
open MLType;

module StringMap = Map.Make(String);

type fullType = (list((option(string), term)), term);

type binding =
  | OL(option(fullType))
  | ML(mlType);

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
    | Schema(body, rest) =>
      {...t, value: Schema(List.map(resolve(env), body), Option.map(resolve(env), rest))}
    | Construct(by, body, rest) =>
      {...t, value: Construct(resolve(env, by), List.map(resolve(env), body), Option.map(resolve(env), rest))}
    | Arrow(l, r) => {...t, value: Arrow(resolve(env, l), resolve(env, r))}
    | Eq(l, r) => {...t, value: Eq(resolve(env, l), resolve(env, r))}
    | Comma(l, r) => {...t, value: Comma(resolve(env, l), resolve(env, r))}
    | BinOp(op, l, r) => {...t, value: BinOp(op, resolve(env, l), resolve(env, r))}
    | List(items) => {...t, value: List(List.map(resolve(env), items))}
    | Fun(pat, body) => {...t, value: Fun(resolve(env, pat), resolve(env, body))}
    | Match(scrut, branches) =>
      {...t, value: Match(resolve(env, scrut), List.map(((p, b)) => (resolve(env, p), resolve(env, b)), branches))}
    | Let(b, body) => {...t, value: Let(resolve(env, b), resolve(env, body))}
    | If(c, th, el) => {...t, value: If(resolve(env, c), resolve(env, th), resolve(env, el))}
    | StringLit(_) | Hole(_) | Shard(_) | BuilderError => t
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

let consistent = (t1: option(term), t2: option(term)): bool =>
  switch (t1, t2) {
  | (None, _) | (_, None) => true
  | (Some({value: Hole(_), _}), _) | (_, Some({value: Hole(_), _})) => true
  | (Some(a), Some(b)) =>
    switch (a.value, b.value) {
    | (Identifier(v1), Identifier(v2)) => v1 == v2
    | _ => false
    }
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
    | Some(ML(_)) => NotFound
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
           "Inconsitency (expected "
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
       ++ stringOfMode(mode)
       ++ ", found "
       ++ allowedStr
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
  | Identifier("Signature") => Some(MPair(MString, MPair(MList(MPair(MString, MTerm)), MTerm)))
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

/* --- OL scope checking: strict when OL bindings exist, permissive otherwise --- */

let hasOLBindings = (ctx: context): bool =>
  StringMap.exists((_, v) => switch (v) { | OL(_) => true | ML(_) => false }, ctx);

/* Signature = (String, List (String, Term), Term) — name, params, return type */
let signatureType = MPair(MString, MPair(MList(MPair(MString, MTerm)), MTerm));

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

/* --- Combine a list of terms into a single term (mirrors Builder.combineTerms) --- */

let combineBody =
  fun
  | [] => mk(Hole(true))
  | [t] => t
  | [first, ..._] as ts => {
      let last = List.nth(ts, List.length(ts) - 1);
      let t = mk(Ap(first, List.tl(ts)));
      {...t, meta: {...t.meta, start: first.meta.start, end_: last.meta.end_}};
    };

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

  | Schema(body, rest) =>
    let schemaExpr = combineBody(body);
    let (toCheck, annotErrors) =
      switch (schemaExpr.value) {
      | Eq({value: Asc(_name, typeAnnot), _}, rhs) =>
        switch (termToMlType(typeAnnot)) {
        | Some(annotTy) =>
          let errs =
            if (eqType(annotTy, schemaType)) { [] }
            else {
              [mark(
                "Schema type mismatch: annotated "
                ++ printType(annotTy)
                ++ ", expected "
                ++ printType(schemaType),
                typeAnnot.meta.start, typeAnnot.meta.end_,
              )];
            };
          (rhs, errs);
        | None =>
          (rhs, [mark("Invalid type annotation", typeAnnot.meta.start, typeAnnot.meta.end_)])
        }
      | Eq(_, rhs) => (rhs, [])
      | _ => (schemaExpr, [])
      };
    let schemaInfo = checkSchema(ctx, toCheck);
    let info = withErrors(schemaInfo, annotErrors);
    let info =
      switch (rest) {
      | Some(r) => mergeInfos(info, checkTerm(ctx, Program, r))
      | None => info
      };
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  | Construct(_by, body, rest) =>
    let (bodyInfo, finalCtx) = checkDecls(ctx, body);
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
          let ty =
            switch (right.value) {
            | Ap(_, _) =>
              switch (rightInfo.inferred) {
              | Some((_, t)) => t
              | None => right
              }
            | _ => right
            };
          StringMap.singleton(x, OL(Some(([], ty))));
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

and checkSchema = (ctx: context, body: term): staticInfo =>
  checkExpr(ctx, schemaType, body)

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
    | _ =>
      (ctx, withErrors(emptyInfo,
        [mark("List pattern but expected " ++ printType(ty), t.meta.start, t.meta.end_)]))
    }

  | Comma(left, right) =>
    switch (ty) {
    | MPair(tyA, tyB) =>
      let (ctx1, info1) = checkPat(ctx, tyA, left);
      let (ctx2, info2) = checkPat(ctx1, tyB, right);
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
      if (name == "Sort" || !hasOLBindings(ctx)) {
        /* Permissive or known — treat as OL constructor */
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
    | Some(OL(_)) => {...emptyInfo, inferred: mlInferred(MTerm)}
    | None =>
      if (name == "Sort" || !hasOLBindings(ctx)) {
        {...emptyInfo, inferred: mlInferred(MTerm)}
      } else {
        withErrors({...emptyInfo, inferred: mlInferred(MTerm)},
          [mark("Unbound variable " ++ name, t.meta.start, t.meta.end_)])
      }
    }

  | StringLit(_) => {...emptyInfo, inferred: mlInferred(MString)}

  | Hole(_) =>
    {errors: [], holes: [(t.meta.start, {goal: hole, context: ctx})],
     inferred: mlInferred(MTerm), bindings: StringMap.empty}

  | Ap(f, args) =>
    let fInfo = inferExpr(ctx, f);
    let fTy =
      switch (fInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) {
        | Some(ty) => ty
        | None => MTerm
        }
      | _ => MTerm
      };
    let (retTy, argInfo) =
      List.fold_left(
        ((accTy, accInfo), arg) =>
          switch (accTy) {
          | MArrow(paramTy, retTy) =>
            let aInfo = checkExpr(ctx, paramTy, arg);
            (retTy, mergeInfos(accInfo, aInfo));
          | MTerm =>
            let aInfo = checkExpr(ctx, MTerm, arg);
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

  | Fun(_, _) =>
    withErrors({...emptyInfo, inferred: mlInferred(MTerm)},
      [mark("Cannot infer type of fun without context", t.meta.start, t.meta.end_)])

  | Let(binding, body) =>
    ignore(binding);
    inferExpr(ctx, body)

  | Match(scrut, branches) =>
    let scrutInfo = inferExpr(ctx, scrut);
    let scrutTy =
      switch (scrutInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    switch (branches) {
    | [] =>
      withErrors(mergeInfos(scrutInfo, {...emptyInfo, inferred: mlInferred(MTerm)}),
        [mark("Empty match", t.meta.start, t.meta.end_)])
    | [(pat, body), ...rest] =>
      let (patCtx, patInfo) = checkPat(ctx, scrutTy, pat);
      let bodyInfo = inferExpr(patCtx, body);
      let bodyTy =
        switch (bodyInfo.inferred) {
        | Some(([], t)) =>
          switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
        | _ => MTerm
        };
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
      switch (thenInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    let elseInfo = checkExpr(ctx, thenTy, elseBr);
    let info = mergeInfos(condInfo, mergeInfos(thenInfo, elseInfo));
    {...info, inferred: mlInferred(thenTy)};

  | Comma(left, right) =>
    let leftInfo = inferExpr(ctx, left);
    let rightInfo = inferExpr(ctx, right);
    let leftTy =
      switch (leftInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    let rightTy =
      switch (rightInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    let info = mergeInfos(leftInfo, rightInfo);
    {...info, inferred: mlInferred(MPair(leftTy, rightTy))};

  | List([]) => {...emptyInfo, inferred: mlInferred(MList(MTerm))}
  | List([first, ...rest]) =>
    let firstInfo = inferExpr(ctx, first);
    let elemTy =
      switch (firstInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    let restInfo =
      List.fold_left(
        (accInfo, item) => mergeInfos(accInfo, checkExpr(ctx, elemTy, item)),
        emptyInfo,
        rest,
      );
    let info = mergeInfos(firstInfo, restInfo);
    {...info, inferred: mlInferred(MList(elemTy))};

  | Postulate(_, _) | Schema(_, _) | Construct(_, _, _) =>
    {...emptyInfo, inferred: mlInferred(MTerm)}

  | BinOp(op, left, right) =>
    switch (op) {
    | "!=" | "==" =>
      let leftInfo = inferExpr(ctx, left);
      let leftTy =
        switch (leftInfo.inferred) {
        | Some(([], t)) =>
          switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
        | _ => MTerm
        };
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
      switch (scrutInfo.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
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
        switch (info.inferred) {
        | Some(([], t)) =>
          switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
        | _ => MTerm
        };
      withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
    }

  | _ =>
    let info = inferExpr(ctx, t);
    let got =
      switch (info.inferred) {
      | Some(([], t)) =>
        switch (termToMlType(t)) { | Some(ty) => ty | None => MTerm }
      | _ => MTerm
      };
    withErrors(info, mlSubsume(expected, got, t.meta.start, t.meta.end_));
  };

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
