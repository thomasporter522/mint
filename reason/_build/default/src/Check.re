open Term;
open Print;
open Error;

module StringMap = Map.Make(String);

type fullType = (list((option(string), term)), term);
type context = StringMap.t(option(fullType));

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
    | Schema(rest) =>
      {...t, value: Schema(Option.map(resolve(env), rest))}
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

/* --- Context lookup --- */

type lookupResult =
  | Found(option(fullType))
  | NotFound;

let sortTerm = mk(Identifier("Sort"));

let lookupCtx = (ctx: context, x: string): lookupResult =>
  if (x == "Sort") {
    Found(Some(([], sortTerm)));
  } else {
    switch (StringMap.find_opt(x, ctx)) {
    | Some(ft) => Found(ft)
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

let lineBinding = (left: term, right: term): context =>
  switch (left.value) {
  | Identifier(x) =>
    StringMap.singleton(x, Some(([], right)))
  | Ap(f, args) =>
    switch (f.value) {
    | Identifier(x) =>
      StringMap.singleton(x, Some((extractParams(args), right)))
    | _ => StringMap.empty
    }
  | _ => StringMap.empty
  };

/* === Main checker === */

let rec checkTerm = (ctx: context, mode: checkingMode, t: term): staticInfo =>
  switch (t.value) {
  | Postulate(body, rest) =>
    let (info, finalCtx) =
      List.fold_left(
        ((accInfo, accCtx), line) => {
          let lineInfo = checkTerm(accCtx, Line, line);
          let newCtx = mergeBindings(accCtx, lineInfo.bindings);
          (mergeInfos(accInfo, lineInfo), newCtx);
        },
        (emptyInfo, ctx),
        body,
      );
    let info = withBindings(info, finalCtx);
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
          /* For applications on the RHS, use the inferred return type
             so that e.g. (f Sort) is stored as Sort, not the raw syntax.
             For everything else (identifiers, holes), keep the raw term. */
          let ty =
            switch (right.value) {
            | Ap(_, _) =>
              switch (rightInfo.inferred) {
              | Some((_, t)) => t
              | None => right
              }
            | _ => right
            };
          StringMap.singleton(x, Some(([], ty)));
        | Ap(f, args) =>
          /* Function declaration: keep raw return type for substitution */
          switch (f.value) {
          | Identifier(x) =>
            StringMap.singleton(x, Some((extractParams(args), right)))
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
          withBindings(info, StringMap.singleton(x, Some(([], right))))
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
      /* Sequential top-level blocks: check each with accumulated context */
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

  | _ => emptyInfo
  };

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
