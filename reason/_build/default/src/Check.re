open Term;
open Print;
open Error;

module StringMap = Map.Make(String);

type proposition = term;
type fullType = (list(term), term);
type context = StringMap.t(option(fullType));

type holeInfo = {
  goal: proposition,
  context,
};

type staticInfo = {
  errors: list(error),
  holes: list((int, holeInfo)),
  inferred: option(fullType),
  bindings: context,
};

let hole: term = meta(Hole(false));
let fullHole: fullType = ([], hole);

let combineBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let rec combineInfos = (infos: list(staticInfo)): staticInfo =>
  switch (infos) {
  | [] => {errors: [], holes: [], inferred: None, bindings: StringMap.empty}
  | [info] => info
  | [info1, info2, ...rest] =>
    let combined = {
      errors: info1.errors @ info2.errors,
      holes: info1.holes @ info2.holes,
      inferred: None,
      bindings: combineBindings(info1.bindings, info2.bindings),
    };
    combineInfos([combined, ...rest]);
  };

let addErrors = (info: staticInfo, errors: list(error)): staticInfo => {
  {...info, errors: info.errors @ errors};
};

let addBindings = (info: staticInfo, bindings: context): staticInfo => {
  {...info, bindings: combineBindings(info.bindings, bindings)};
};

type checkingMode =
  | Program
  | Line
  | Spine
  | Argument
  | IdentifierMode
  | Expression(option(term));

let combine =
    (ts1: option(term), ts2: option(term))
    : (bool, option(term)) =>
  switch (ts1, ts2) {
  | (None, _)
  | (_, None) => (true, None)
  | (Some(t1), Some(t2)) =>
    switch (t1.value, t2.value) {
    | (Hole(_), _)
    | (_, Hole(_)) => (true, Some(hole))
    | (Identifier(v1), Identifier(v2)) when v1 == v2 => (true, Some(t1))
    | _ when t1.value != t2.value => (false, Some(hole))
    | _ => (false, Some(hole))
    }
  };

let inCtx =
    (ctx: context, x: string): (bool, option(fullType)) =>
  if (x == "U") {
    (true, None);
  } else {
    switch (StringMap.find_opt(x, ctx)) {
    | Some(ft) => (true, ft)
    | None => (false, Some(([], hole)))
    };
  };

let subsume =
    (
      mode: checkingMode,
      from: int,
      to_: int,
      inferred: option(fullType),
      errors: list(error),
    )
    : list(error) =>
  switch (mode) {
  | Expression(expected) =>
    let errors =
      switch (inferred) {
      | Some((args, _)) when List.length(args) > 0 && expected != None =>
        [{type_: "mark", message: "Too few arguments", from, to_}, ...errors]
      | _ => errors
      };
    let inferredOut =
      switch (inferred) {
      | Some((_, out)) => Some(out)
      | None => None
      };
    let (consistent, _) = combine(expected, inferredOut);
    if (!consistent) {
      switch (expected, inferredOut) {
      | (Some(exp), Some(inf)) =>
        let err = {
          type_: "mark",
          message:
            "Inconsitency (expected "
            ++ printTerm(exp)
            ++ ", got "
            ++ printTerm(inf)
            ++ ")",
          from,
          to_,
        };
        [err, ...errors];
      | _ => errors
      };
    } else {
      errors;
    };
  | _ => errors
  };

let countArgs =
    (
      argsExpected: int,
      argsFound: int,
      from: int,
      to_: int,
      errors: list(error),
    )
    : list(error) =>
  if (argsExpected == argsFound) {
    errors;
  } else {
    let msg =
      argsExpected > argsFound ? "Too few arguments" : "Too many arguments";
    [{type_: "mark", message: msg, from, to_}, ...errors];
  };

let ensureMode =
    (
      allowed: list(string),
      mode: checkingMode,
      from: int,
      to_: int,
      errors: list(error),
    )
    : list(error) => {
  let modeStr =
    switch (mode) {
    | Program => "program"
    | Line => "line"
    | Spine => "spine"
    | Argument => "argument"
    | IdentifierMode => "identifier"
    | Expression(_) => "expression"
    };
  if (!List.mem(modeStr, allowed)) {
    let allowedStr = String.concat(",", allowed);
    [
      {
        type_: "mark",
        message:
          "Sort error (expected "
          ++ modeStr
          ++ ", found "
          ++ allowedStr
          ++ ")",
        from,
        to_,
      },
      ...errors,
    ];
  } else {
    errors;
  };
};

let rec checkTerm =
        (ctx: context, mode: checkingMode, t: term): staticInfo =>
  switch (t.value) {
  | Postulate(body, _rest) =>
    let (infos, finalCtx) =
      List.fold_left(
        ((accInfo, accCtx), line) => {
          let info = checkTerm(accCtx, Line, line);
          let combined = combineInfos([accInfo, info]);
          let newCtx = combineBindings(accCtx, info.bindings);
          (combined, newCtx);
        },
        (combineInfos([]), ctx),
        body,
      );
    let infos = addBindings(infos, finalCtx);
    let errors =
      ensureMode(["program"], mode, t.meta.start, t.meta.end_, []);
    addErrors(infos, errors);

  | Identifier(v) =>
    let inferred = ref(None);
    let errors =
      ensureMode(
        ["expression", "spine", "identifier"],
        mode,
        t.meta.start,
        t.meta.end_,
        [],
      );
    let errors =
      switch (mode) {
      | Expression(_) =>
        let (valid, inf) = inCtx(ctx, v);
        inferred := inf;
        let errors =
          if (!valid) {
            [
              {
                type_: "mark",
                message: "Unbound variable " ++ v,
                from: t.meta.start,
                to_: t.meta.end_,
              },
              ...errors,
            ];
          } else {
            errors;
          };
        switch (inf) {
        | Some(_) =>
          subsume(mode, t.meta.start, t.meta.end_, inf, errors)
        | None => errors
        };
      | _ => errors
      };
    {errors, holes: [], inferred: inferred^, bindings: StringMap.empty};

  | Asc(left, right) =>
    switch (mode) {
    | Line =>
      let infos = checkTerm(ctx, Spine, left);
      let infos =
        combineInfos([
          infos,
          checkTerm(
            combineBindings(ctx, infos.bindings),
            Expression(Some(hole)),
            right,
          ),
        ]);
      let bindings =
        switch (left.value) {
        | Identifier(x) =>
          StringMap.singleton(x, Some(([], right)))
        | Ap(f, args) =>
          switch (f.value) {
          | Identifier(x) =>
            StringMap.singleton(x, Some((args, right)))
          | _ => StringMap.empty
          }
        | _ => StringMap.empty
        };
      {...infos, bindings};
    | Argument =>
      let leftInfo = checkTerm(ctx, IdentifierMode, left);
      let rightInfo = checkTerm(ctx, Expression(Some(hole)), right);
      let infos = combineInfos([leftInfo, rightInfo]);
      let infos =
        if (List.length(leftInfo.errors) == 0) {
          switch (left.value) {
          | Identifier(x) =>
            addBindings(
              infos,
              StringMap.singleton(x, Some(([], right))),
            )
          | _ => infos
          };
        } else {
          infos;
        };
      infos;
    | _ =>
      let errors =
        ensureMode(
          ["argument"],
          mode,
          t.meta.start,
          t.meta.end_,
          [],
        );
      let infos =
        combineInfos([
          checkTerm(ctx, Expression(Some(hole)), left),
          checkTerm(ctx, Expression(Some(hole)), right),
        ]);
      addErrors(infos, errors);
    }

  | Ap(f, args) =>
    switch (mode) {
    | Spine =>
      let infos = checkTerm(ctx, IdentifierMode, f);
      let currentCtx = ref(combineBindings(ctx, infos.bindings));
      let infos = ref(infos);
      List.iter(
        arg => {
          infos :=
            combineInfos([infos^, checkTerm(currentCtx^, Argument, arg)]);
          currentCtx := combineBindings(currentCtx^, (infos^).bindings);
        },
        args,
      );
      infos^;
    | Expression(_) =>
      let infos = checkTerm(ctx, Expression(None), f);
      let funtype = infos.inferred;
      let errors = ref([]);
      let infos = ref(infos);
      switch (funtype) {
      | Some((argTypes, retType)) =>
        errors :=
          countArgs(
            List.length(argTypes),
            List.length(args),
            f.meta.start,
            f.meta.end_,
            errors^,
          );
        let minLen = min(List.length(argTypes), List.length(args));
        for (i in 0 to minLen - 1) {
          let argType = List.nth(argTypes, i);
          let arg = List.nth(args, i);
          infos :=
            combineInfos([
              infos^,
              checkTerm(ctx, Expression(Some(argType)), arg),
            ]);
        };
        let inferred =
          if (List.length(argTypes) == List.length(args)) {
            retType;
          } else {
            hole;
          };
        infos := {...infos^, inferred: Some(([], inferred))};
        errors :=
          subsume(
            mode,
            t.meta.start,
            t.meta.end_,
            (infos^).inferred,
            errors^,
          );
      | None => ()
      };
      addErrors(infos^, errors^);
    | _ =>
      let errors =
        ensureMode(["spine"], mode, t.meta.start, t.meta.end_, []);
      let infos = checkTerm(ctx, Expression(Some(hole)), f);
      let argInfos =
        List.map(c => checkTerm(ctx, Expression(Some(hole)), c), args);
      addErrors(combineInfos([infos, ...argInfos]), errors);
    }

  | Hole(_) =>
    switch (mode) {
    | Expression(expected) =>
      let expected =
        switch (expected) {
        | Some(e) => e
        | None => hole
        };
      let holes = [(t.meta.start, {goal: expected, context: ctx})];
      {errors: [], holes, inferred: Some(fullHole), bindings: StringMap.empty};
    | _ =>
      let err = {
        type_: "mark",
        message: "Hole in non-expression",
        from: t.meta.start,
        to_: t.meta.end_,
      };
      {
        errors: [err],
        holes: [],
        inferred: Some(fullHole),
        bindings: StringMap.empty,
      };
    }

  | _ => combineInfos([])
  };

let getStatics = (t: term): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
