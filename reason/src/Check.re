open Term;
open Print;
open Error;
open MLType;

module StringMap = Map.Make(String);

type fullType = (list((option(string), ol)), ol);

type binding =
  | OL(option(fullType))
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
  inferred: option(fullType),
  mlInferred: option(mlType),
  bindings: context,
};

let olHole: ol = mkOL(OLHole(User));
let mlHole: ml = mkML(Hole(Synthesized));
let fullHole: fullType = ([], olHole);

let emptyInfo = {errors: [], holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty};

/* MetaLet definitions in definition order, for eval env construction.
   Set by Meta block processing, read by Construct block. */
let metaDefsRef: ref(list((string, ml))) = ref([]);

let mergeBindings = (c1: context, c2: context): context =>
  StringMap.union((_key, _v1, v2) => Some(v2), c1, c2);

let mergeInfos = (i1: staticInfo, i2: staticInfo): staticInfo => {
  errors: i1.errors @ i2.errors,
  holes: i1.holes @ i2.holes,
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
    | OLHole(_) => t
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
    | OLHole(_) => t
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

/* --- Type consistency --- */

/* Structural consistency: like equality but holes match anything */
let rec termConsistent = (a: ol, b: ol): bool =>
  switch (a.value, b.value) {
  | (OLHole(_), _) | (_, OLHole(_)) => true
  | (OLIdentifier(x), OLIdentifier(y)) => x == y
  | (OLAp(f1, args1), OLAp(f2, args2)) =>
    termConsistent(f1, f2)
    && List.length(args1) == List.length(args2)
    && List.for_all2(termConsistent, args1, args2)
  | _ => false
  };

let consistent = (t1: option(ol), t2: option(ol)): bool =>
  switch (t1, t2) {
  | (None, _) | (_, None) => true
  | (Some(a), Some(b)) => termConsistent(a, b)
  };

/* --- Context lookup (OL mode) --- */

type lookupResult =
  | Found(option(fullType))
  | NotFound;

let sortTerm = mkOL(OLIdentifier("Sort"));

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
    (expected: option(ol), inferred: option(fullType), from, to_)
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
           ++ printOL(exp)
           ++ ", got "
           ++ printOL(inf)
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

/* --- Extracting params (name + type) from OL arg list --- */

let extractParams = (args: list(ol)): list((option(string), ol)) =>
  List.map(
    (arg: ol) =>
      switch (arg.value) {
      | OLAp({value: OLIdentifier(":"), _}, [name, ty]) =>
        let paramName =
          switch (name.value) {
          | OLIdentifier(v) => Some(v)
          | _ => None
          };
        (paramName, ty);
      | _ => (None, arg)
      },
    args,
  );

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
  StringMap.exists((_, v) => switch (v) { | OL(_) => true | ML(_) | Builtin(_) | SchemaBinding(_) | MetaLet(_, _) => false }, ctx);

/* Signature = (Term, List (Term, Term), Term) — name, params, return type.
   Matches Eval.declToSignature: Tuple([name, List(params), retType]) */
let signatureType = MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm]);

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

/* ML builtins context — every ML builtin must be declared here */
let mlBuiltins: context =
  List.fold_left(
    (acc, (name, b)) => StringMap.add(name, b, acc),
    StringMap.empty,
    [
      /* OL constant available in ML */
      ("Sort", ML(MTerm)),
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

/* === Helpers: parse ML-encoded declarations and meta defs === */

/* Parse an ML-encoded declaration back to a decl.
   Encoding: Ap(Identifier(":"), [lhs, retType])
   where lhs is Identifier(name) or Ap(Identifier(name), [param1, ...])
   and each param is Ap(Identifier(":"), [Identifier(pname), typeExpr]) */
let parseDeclFromML = (t: ml): decl =>
  switch (t.value) {
  | Ap({value: Identifier(":"), _}, [lhs, retTypeExpr]) =>
    switch (lhs.value) {
    | Identifier(name) =>
      {declName: name, params: [], retType: mlToOL(retTypeExpr), declMeta: t.meta}
    | Ap({value: Identifier(name), _}, paramExprs) =>
      let params = List.map((p: ml) =>
        switch (p.value) {
        | Ap({value: Identifier(":"), _}, [{value: Identifier(pname), _}, typeExpr]) =>
          {paramName: pname, paramType: mlToOL(typeExpr), paramMeta: p.meta}
        | Identifier(pname) =>
          {paramName: pname, paramType: mkOL(OLHole(Synthesized)), paramMeta: p.meta}
        | _ =>
          {paramName: "_", paramType: mkOL(OLHole(Synthesized)), paramMeta: p.meta}
        },
        paramExprs,
      );
      {declName: name, params, retType: mlToOL(retTypeExpr), declMeta: t.meta}
    | _ =>
      {declName: "_", params: [], retType: mlToOL(retTypeExpr), declMeta: t.meta}
    }
  | Identifier(name) =>
    {declName: name, params: [], retType: mkOL(OLHole(Synthesized)), declMeta: t.meta}
  | _ =>
    {declName: "_", params: [], retType: mkOL(OLHole(Synthesized)), declMeta: t.meta}
  };


/* === Unified checker: OL and ML mutually recursive === */

let rec checkDecls = (ctx: context, items: list(ml)): (staticInfo, context) => {
  let decls = List.map(parseDeclFromML, items);
  List.fold_left(
    ((accInfo, accCtx), d: decl) => {
      let lineInfo = checkDeclLine(accCtx, d);
      let newCtx = mergeBindings(accCtx, lineInfo.bindings);
      (mergeInfos(accInfo, lineInfo), newCtx);
    },
    (emptyInfo, ctx),
    decls,
  );
}

/* Check a single declaration line: (name (p1:T1) ...) : RetType */
and checkDeclLine = (ctx: context, d: decl): staticInfo => {
  /* Build a context with parameters */
  let paramCtx = List.fold_left(
    (acc, p: param) =>
      StringMap.add(p.paramName, OL(Some(([], p.paramType))), acc),
    ctx,
    d.params,
  );
  /* Check retType is well-formed in that context */
  let retInfo = checkOLTerm(paramCtx, Expression(Some(olHole)), d.retType);
  /* Build the fullType for this declaration */
  let paramPairs = List.map(
    (p: param) => (Some(p.paramName), p.paramType),
    d.params,
  );
  let bindings = StringMap.singleton(d.declName, OL(Some((paramPairs, d.retType))));
  {...retInfo, bindings};
}

/* Check an OL term (used for declaration types in postulate/construct) */
and checkOLTerm = (ctx: context, mode: checkingMode, t: ol): staticInfo =>
  switch (t.value) {
  | OLIdentifier(v) =>
    let modeErrors = ensureMode(
      ["expression", "spine", "identifier"], mode, t.meta.start, t.meta.end_,
    );
    switch (mode) {
    | Expression(_) =>
      switch (lookupCtx(ctx, v)) {
      | NotFound =>
        let err = mark("Unbound variable " ++ v, t.meta.start, t.meta.end_);
        {errors: [err, ...modeErrors], holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
      | Found(inferred) =>
        let subErrors =
          switch (mode) {
          | Expression(expected) => subsume(expected, inferred, t.meta.start, t.meta.end_)
          | _ => []
          };
        {errors: modeErrors @ subErrors, holes: [], inferred, mlInferred: None, bindings: StringMap.empty};
      }
    | _ =>
      {errors: modeErrors, holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty}
    };

  | OLAp(f, args) =>
    switch (mode) {
    | Spine =>
      let (info, _) =
        List.fold_left(
          ((accInfo, accCtx), arg) => {
            let argInfo = checkOLTerm(accCtx, Argument, arg);
            let combined = mergeInfos(accInfo, argInfo);
            (combined, mergeBindings(accCtx, combined.bindings));
          },
          {
            let funInfo = checkOLTerm(ctx, IdentifierMode, f);
            (funInfo, mergeBindings(ctx, funInfo.bindings));
          },
          args,
        );
      info;

    | Expression(expected) =>
      let funInfo = checkOLTerm(ctx, Expression(None), f);
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
              let argInfo = checkOLTerm(ctx, Expression(Some(expectedTy)), List.nth(args, i));
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
            ? Some(([], retType)) : Some(([], olHole));
        let subErrors = subsume(expected, inferred, t.meta.start, t.meta.end_);
        withErrors({...info, inferred}, arityErrors @ subErrors);
      | None => funInfo
      };

    | _ =>
      let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
      let funInfo = checkOLTerm(ctx, Expression(Some(olHole)), f);
      let argInfos = List.map(a => checkOLTerm(ctx, Expression(Some(olHole)), a), args);
      withErrors(List.fold_left(mergeInfos, funInfo, argInfos), modeErrors);
    }

  | OLHole(_) =>
    switch (mode) {
    | Expression(expected) =>
      let goal =
        switch (expected) {
        | Some(e) => embedOL(e)
        | None => mlHole
        };
      {errors: [], holes: [(t.meta.start, {goal, context: ctx})],
       inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
    | _ =>
      {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
       holes: [], inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
    }
  }

/* Check an ML expression in the program-level / block context.
   Handles __seq, __postulate, __meta, __construct encodings,
   plus regular ML expressions. */
and checkTerm = (ctx: context, mode: checkingMode, t: ml): staticInfo =>
  switch (t.value) {
  /* __seq: sequential block chaining */
  | Ap({value: Identifier("__seq"), _}, [first, rest]) =>
    let firstInfo = checkTerm(ctx, Program, first);
    let nextCtx = mergeBindings(ctx, firstInfo.bindings);
    let restInfo = checkTerm(nextCtx, Program, rest);
    mergeInfos(firstInfo, restInfo);

  /* __postulate: declaration block */
  | Ap({value: Identifier("__postulate"), _}, items) =>
    let (info, finalCtx) = checkDecls(ctx, items);
    let info = withBindings(info, finalCtx);
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  /* __meta: meta definition block */
  | Ap({value: Identifier("__meta"), _}, items) =>
    let mlCtx = StringMap.union((_, _, v) => Some(v), ctx, mlBuiltins);
    let (metaInfo, metaCtx, metaDefs) = processMeta(emptyInfo, mlCtx, [], items);
    metaDefsRef := metaDefs;
    withErrors(metaInfo, ensureMode(["program"], mode, t.meta.start, t.meta.end_))
    |> (info => withBindings(info, metaCtx));

  /* __construct: construct block with schema */
  | Ap({value: Identifier("__construct"), _}, [schemaRef, ...declItems]) =>
    let (bodyInfo, finalCtx) = checkDecls(ctx, declItems);
    let decls = List.map(parseDeclFromML, declItems);
    /* Run the schema on the construct declarations and type-check witnesses */
    let witnessErrors =
      switch (schemaRef.value) {
      | Identifier(schemaName) =>
        switch (StringMap.find_opt(schemaName, ctx)) {
        | Some(SchemaBinding(schemaBody)) =>
          /* Build eval env from MetaLet definitions in definition order.
             First pass: evaluate each body with the env built so far.
             Second pass: patch all closures to see the complete env. */
          let rawEnv = List.fold_left(
            (acc, (name, defBody)) =>
              switch (Eval.evalExpr(acc, defBody)) {
              | Eval.Ok(v) => Eval.StringMap.add(name, v, acc)
              | Eval.Err(_) => acc
              },
            Eval.StringMap.empty,
            metaDefsRef^,
          );
          let evalEnv = Eval.StringMap.map(
            fun
            | Eval.Closure(_, pat, body) => Eval.Closure(rawEnv, pat, body)
            | v => v,
            rawEnv,
          );
          switch (Eval.evalExpr(evalEnv, schemaBody)) {
          | Eval.Ok(schemaVal) =>
            switch (Eval.runSchema(schemaVal, decls)) {
            | Eval.Witnesses(witnesses) =>
              /* Check witness count matches declaration count */
              if (List.length(witnesses) != List.length(decls)) {
                [mark(
                  "Schema produced " ++ string_of_int(List.length(witnesses))
                  ++ " witnesses but construct has " ++ string_of_int(List.length(decls))
                  ++ " declarations",
                  schemaRef.meta.start, schemaRef.meta.end_,
                )];
              } else {
                /* Substitute witnesses for declared constants and type-check.
                   For each declaration, the witness must have the declared type
                   in the context where previous witnesses have been substituted. */
                let (witnessErrs, _) = List.fold_left2(
                  ((accErrs, substEnv), d: decl, witness) => {
                    /* Add declaration parameters to context for witness checking.
                       Parameter types must be resolved through substEnv so that
                       references to earlier declared names get their witnesses. */
                    let witnessCtx =
                      List.fold_left(
                        (acc, p: param) => {
                          let resolvedPty = resolveWithParams(substEnv, p.paramType);
                          StringMap.add(p.paramName, OL(Some(([], resolvedPty))), acc);
                        },
                        ctx,
                        d.params,
                      );
                    let expectedType = resolveWithParams(substEnv, d.retType);
                    let witnessInfo = checkOLTerm(witnessCtx, Expression(Some(expectedType)), mlToOL(witness));
                    /* For parameterized decls, store (name, params, witness) for
                       application-level substitution in subsequent types */
                    let paramNames = List.map((p: param) => p.paramName, d.params);
                    let newSubstEnv =
                      StringMap.add(d.declName, (paramNames, witness), substEnv);
                    (accErrs @ witnessInfo.errors, newSubstEnv);
                  },
                  ([], emptyWitnessEnv),
                  decls,
                  witnesses,
                );
                if (List.length(witnessErrs) > 0) {
                  let details = String.concat("; ", List.map((e: error) => e.message, witnessErrs));
                  [mark(
                    schemaName ++ " matched but generated ill-typed witnesses: " ++ details,
                    schemaRef.meta.start, schemaRef.meta.end_,
                  )];
                } else {
                  [];
                };
              }
            | Eval.SchemaError(msg) =>
              [mark("Schema error: " ++ msg, schemaRef.meta.start, schemaRef.meta.end_)]
            }
          | Eval.Err(msg) =>
            [mark("Schema evaluation failed: " ++ msg, schemaRef.meta.start, schemaRef.meta.end_)]
          }
        | Some(_) =>
          [mark(schemaName ++ " is not a schema", schemaRef.meta.start, schemaRef.meta.end_)]
        | None =>
          [mark("Schema " ++ schemaName ++ " not found", schemaRef.meta.start, schemaRef.meta.end_)]
        }
      | _ => []
      };
    let info = withErrors(bodyInfo, witnessErrors);
    let info = withBindings(info, finalCtx);
    withErrors(info, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  /* __construct with no declarations */
  | Ap({value: Identifier("__construct"), _}, _) =>
    withErrors(emptyInfo, ensureMode(["program"], mode, t.meta.start, t.meta.end_));

  /* --- Regular ML expression handling --- */

  | Identifier(v) =>
    let modeErrors = ensureMode(
      ["expression", "spine", "identifier"], mode, t.meta.start, t.meta.end_,
    );
    switch (mode) {
    | Expression(_) =>
      switch (lookupCtx(ctx, v)) {
      | NotFound =>
        let err = mark("Unbound variable " ++ v, t.meta.start, t.meta.end_);
        {errors: [err, ...modeErrors], holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
      | Found(inferred) =>
        let subErrors =
          switch (mode) {
          | Expression(expected) => subsume(expected, inferred, t.meta.start, t.meta.end_)
          | _ => []
          };
        {errors: modeErrors @ subErrors, holes: [], inferred, mlInferred: None, bindings: StringMap.empty};
      }
    | _ =>
      {errors: modeErrors, holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty}
    };

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
                | Some(name) => StringMap.add(name, List.nth(args, i) |> mlToOL, env)
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
            ? Some(([], retType)) : Some(([], olHole));
        let subErrors = subsume(expected, inferred, t.meta.start, t.meta.end_);
        withErrors({...info, inferred}, arityErrors @ subErrors);
      | None => funInfo
      };

    | Line =>
      /* OL declaration line encoded as Ap(Identifier(":"), [lhs, retType]) */
      switch (f.value) {
      | Identifier(":") =>
        switch (args) {
        | [_left, _right] =>
          let d = parseDeclFromML(t);
          checkDeclLine(ctx, d);
        | _ => emptyInfo
        }
      | _ =>
        let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
        let funInfo = checkTerm(ctx, Expression(Some(olHole)), f);
        let argInfos = List.map(a => checkTerm(ctx, Expression(Some(olHole)), a), args);
        withErrors(List.fold_left(mergeInfos, funInfo, argInfos), modeErrors);
      }

    | Argument =>
      /* Argument in OL spine: Ap(Identifier(":"), [name, type]) */
      switch (f.value) {
      | Identifier(":") =>
        switch (args) {
        | [{value: Identifier(x), _} as left, right] =>
          let leftInfo = checkTerm(ctx, IdentifierMode, left);
          let rightInfo = checkTerm(ctx, Expression(Some(olHole)), right);
          let info = mergeInfos(leftInfo, rightInfo);
          if (List.length(leftInfo.errors) == 0) {
            withBindings(info, StringMap.singleton(x, OL(Some(([], mlToOL(right))))))
          } else {
            info;
          };
        | _ => emptyInfo
        }
      | _ =>
        let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
        let funInfo = checkTerm(ctx, Expression(Some(olHole)), f);
        let argInfos = List.map(a => checkTerm(ctx, Expression(Some(olHole)), a), args);
        withErrors(List.fold_left(mergeInfos, funInfo, argInfos), modeErrors);
      }

    | _ =>
      let modeErrors = ensureMode(["spine"], mode, t.meta.start, t.meta.end_);
      let funInfo = checkTerm(ctx, Expression(Some(olHole)), f);
      let argInfos = List.map(a => checkTerm(ctx, Expression(Some(olHole)), a), args);
      withErrors(List.fold_left(mergeInfos, funInfo, argInfos), modeErrors);
    }

  | Hole(_) =>
    switch (mode) {
    | Expression(expected) =>
      let goal =
        switch (expected) {
        | Some(e) => embedOL(e)
        | None => mlHole
        };
      {errors: [], holes: [(t.meta.start, {goal, context: ctx})],
       inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
    | _ =>
      {errors: [mark("Hole in non-expression", t.meta.start, t.meta.end_)],
       holes: [], inferred: Some(fullHole), mlInferred: None, bindings: StringMap.empty};
    }

  | Shard(_) =>
    if (t.meta.start >= 0) {
      {errors: [mark("Unexpected token", t.meta.start, t.meta.end_)],
       holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
    } else {
      emptyInfo;
    }

  | BuilderError =>
    if (t.meta.start >= 0) {
      {errors: [mark("Syntax error", t.meta.start, t.meta.end_)],
       holes: [], inferred: None, mlInferred: None, bindings: StringMap.empty};
    } else {
      emptyInfo;
    }

  | _ => emptyInfo
  }

/* === Process meta definitions === */

and processMeta = (accInfo, accCtx, accDefs, items: list(ml)):
    (staticInfo, context, list((string, ml))) =>
  switch (items) {
  | [] => (accInfo, accCtx, accDefs)

  /* schema name = body */
  | [{value: Ap({value: Identifier("schema"), _}, innerItems), _}, ...rest] =>
    /* Parse schema binding from the ML encoding */
    let (name, annotation, rhs) = parseMetaBinding(innerItems);
    let schemaInfo = checkSchema(accCtx, rhs);
    let annotErrors =
      switch (annotation) {
      | Some(Some(annotTy)) =>
        if (eqType(annotTy, schemaType)) { [] }
        else {
          [mark(
            "Schema type mismatch: annotated "
            ++ printType(annotTy)
            ++ ", expected "
            ++ printType(schemaType),
            -1, -1,
          )];
        }
      | Some(None) =>
        [mark("Invalid type annotation", -1, -1)]
      | None => []
      };
    let info = withErrors(mergeInfos(accInfo, schemaInfo), annotErrors);
    let newCtx =
      switch (name) {
      | Some(n) => StringMap.add(n, SchemaBinding(rhs), accCtx)
      | None => accCtx
      };
    processMeta(info, newCtx, accDefs, rest);

  /* name : type = body  OR  name = body */
  | [{value: Ap({value: Identifier("="), _}, eqArgs), _} as item, ...rest] =>
    let (name, annotation, rhs) = parseMetaLetBinding(eqArgs, item);
    switch (name) {
    | Some(n) =>
      let (bodyInfo, rhsTy) =
        switch (annotation) {
        | Some(ty) => (checkExpr(accCtx, ty, rhs), ty)
        | None =>
          let info = inferExpr(accCtx, rhs);
          (info, getInferredMlType(info));
        };
      let newCtx = StringMap.add(n, MetaLet(rhs, rhsTy), accCtx);
      let newDefs = accDefs @ [(n, rhs)];
      processMeta(mergeInfos(accInfo, bodyInfo), newCtx, newDefs, rest);
    | None =>
      let bodyInfo = inferExpr(accCtx, rhs);
      processMeta(mergeInfos(accInfo, bodyInfo), accCtx, accDefs, rest);
    }

  /* Skip unrecognized items */
  | [item, ...rest] =>
    let itemInfo = inferExpr(accCtx, item);
    processMeta(mergeInfos(accInfo, itemInfo), accCtx, accDefs, rest);
  }

/* Parse a meta schema binding from ML-encoded form.
   Input is the args of Ap(Identifier("schema"), innerItems).
   Returns (name, annotation, rhs).
   annotation: None = no annotation, Some(Some(ty)) = valid, Some(None) = invalid */
and parseMetaBinding = (items: list(ml)): (option(string), option(option(mlType)), ml) =>
  switch (items) {
  | [{value: Ap({value: Identifier("="), _}, [{value: Identifier(name), _}, rhs]), _}] =>
    (Some(name), None, rhs)
  | [{value: Ap({value: Identifier("="), _}, [
      {value: Ap({value: Identifier(":"), _}, [{value: Identifier(name), _}, typeExpr]), _},
      rhs,
    ]), _}] =>
    (Some(name), Some(mlExprToType(typeExpr)), rhs)
  | [rhs] =>
    (None, None, rhs)
  | items =>
    /* Multiple items — combine as application */
    switch (items) {
    | [] => (None, None, mkML(Hole(Synthesized)))
    | [single] => (None, None, single)
    | [first, ...rest] => (None, None, mkML(Ap(first, rest)))
    }
  }

/* Parse a meta let binding.
   Input: args of Ap(Identifier("="), eqArgs) and the full item for metadata.
   Returns: (name, annotation, rhs) */
and parseMetaLetBinding = (eqArgs: list(ml), _item: ml): (option(string), option(mlType), ml) =>
  switch (eqArgs) {
  /* name : type = rhs */
  | [{value: Ap({value: Identifier(":"), _}, [{value: Identifier(name), _}, typeExpr]), _}, rhs] =>
    (Some(name), mlExprToType(typeExpr), rhs)
  /* name = rhs */
  | [{value: Identifier(name), _}, rhs] =>
    (Some(name), None, rhs)
  | [_, rhs] =>
    (None, None, rhs)
  | _ =>
    (None, None, mkML(Hole(Synthesized)))
  }

/* === ML checker — total error localization (mutually recursive with checkTerm) === */
/* inferExpr and checkExpr always return staticInfo, never fail.
   Errors are accumulated. inferExpr sets inferred to carry the ML type. */

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
    {errors: [], holes: [(t.meta.start, {goal: mlHole, context: ctx})],
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

  | Shard(_) | BuilderError =>
    withErrors(setMlType(emptyInfo, MTerm),
      [mark("Invalid expression", t.meta.start, t.meta.end_)])
  }

and checkExpr = (ctx: context, expected: mlType, t: ml): staticInfo =>
  switch (t.value) {
  | Hole(_) =>
    let goal = mlTypeToTerm(expected);
    {errors: [], holes: [(t.meta.start, {goal, context: ctx})],
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

let getStatics = (t: ml): staticInfo =>
  checkTerm(StringMap.empty, Program, t);
