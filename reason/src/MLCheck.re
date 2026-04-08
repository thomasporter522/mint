/* ML type checker for the meta-language.
   Checks expressions against the simply-typed ML type system.
   This is UNTRUSTED code — it runs metaprograms, not kernel verification. */

open Term;
open MLType;

module StringMap = Map.Make(String);

type mlEnv = StringMap.t(mlType);

type mlError =
  | TypeError(string, int, int)
  | Unimplemented(string, int, int);

type mlResult('a) =
  | Ok('a)
  | Err(mlError);

let err = (msg, t: term) => Err(TypeError(msg, t.meta.start, t.meta.end_));
let unimpl = (msg, t: term) => Err(Unimplemented(msg, t.meta.start, t.meta.end_));

/* --- Check that an inferred type matches an expected type --- */

let expectType = (expected: mlType, got: mlType, t: term): mlResult(unit) =>
  if (eqType(expected, got)) {
    Ok();
  } else {
    err(
      "Expected " ++ printType(expected) ++ ", got " ++ printType(got),
      t,
    );
  };

/* --- Pattern checking: returns bindings introduced by the pattern --- */

let rec checkPat = (env: mlEnv, ty: mlType, t: term): mlResult(mlEnv) =>
  switch (t.value) {
  /* ?x — pattern binder. First occurrence binds, subsequent = equality constraint.
     For now we just bind (no equality constraint check). */
  /* HACK: ?x is parsed as Identifier("?x") by the lexer */
  | Identifier(name) when String.length(name) > 0 && name.[0] == '?' =>
    let varName = String.sub(name, 1, String.length(name) - 1);
    switch (StringMap.find_opt(varName, env)) {
    | Some(existingTy) =>
      /* Already bound — check types match (equality constraint) */
      switch (expectType(existingTy, ty, t)) {
      | Ok () => Ok(env)
      | Err(_) as e => e
      }
    | None =>
      Ok(StringMap.add(varName, ty, env))
    }

  /* _ — wildcard, matches anything */
  | Identifier("_") => Ok(env)

  /* String literal pattern */
  | StringLit(_) =>
    switch (expectType(MString, ty, t)) {
    | Ok () => Ok(env)
    | Err(_) as e => e
    }

  /* List pattern [p1, p2, ...] */
  | List(items) =>
    switch (ty) {
    | MList(elemTy) =>
      List.fold_left(
        (accResult, item) =>
          switch (accResult) {
          | Err(_) as e => e
          | Ok(accEnv) => checkPat(accEnv, elemTy, item)
          },
        Ok(env),
        items,
      )
    | _ => err("List pattern but expected " ++ printType(ty), t)
    }

  /* Pair pattern (p1, p2) */
  | Comma(left, right) =>
    switch (ty) {
    | MPair(tyA, tyB) =>
      switch (checkPat(env, tyA, left)) {
      | Err(_) as e => e
      | Ok(env1) => checkPat(env1, tyB, right)
      }
    | _ => err("Pair pattern but expected " ++ printType(ty), t)
    }

  /* OL constructor pattern: ident followed by sub-patterns (application).
     All OL terms in patterns have type Term. */
  | Ap(_, _) when eqType(ty, MTerm) =>
    checkOLPat(env, t)

  /* Plain identifier as pattern variable (like ML) */
  | Identifier(name) when !(String.length(name) > 0 && name.[0] == '?') =>
    switch (StringMap.find_opt(name, env)) {
    | Some(existingTy) =>
      switch (expectType(existingTy, ty, t)) {
      | Ok () => Ok(env)
      | Err(_) as e => e
      }
    | None =>
      Ok(StringMap.add(name, ty, env))
    }

  | Hole(_) =>
    /* ? in pattern = wildcard essentially */
    Ok(env)

  | _ => unimpl("Pattern form not yet supported", t)
  }

/* Check an OL term used as a pattern — any ?x inside binds at type Term */
and checkOLPat = (env: mlEnv, t: term): mlResult(mlEnv) =>
  switch (t.value) {
  | Identifier(name) when String.length(name) > 0 && name.[0] == '?' =>
    let varName = String.sub(name, 1, String.length(name) - 1);
    switch (StringMap.find_opt(varName, env)) {
    | Some(_) => Ok(env) /* already bound, equality constraint */
    | None => Ok(StringMap.add(varName, MTerm, env))
    }
  | Identifier(_) => Ok(env)
  | Ap(f, args) =>
    List.fold_left(
      (accResult, arg) =>
        switch (accResult) {
        | Err(_) as e => e
        | Ok(accEnv) => checkOLPat(accEnv, arg)
        },
      checkOLPat(env, f),
      args,
    )
  | Hole(_) => Ok(env)
  | _ => Ok(env)
  };

/* --- Helpers --- */

let combineArgs = (args: list(term)): term =>
  switch (args) {
  | [] => mk(Hole(true))
  | [t] => t
  | [f, ...rest] => mk(Ap(f, rest))
  };

/* --- Expression type inference --- */

let rec inferExpr = (env: mlEnv, t: term): mlResult(mlType) =>
  switch (t.value) {
  /* Identifiers: look up in ML env, or treat as OL Term */
  | Identifier(name) =>
    switch (StringMap.find_opt(name, env)) {
    | Some(ty) => Ok(ty)
    | None =>
      /* Not in ML env — treat as OL identifier (type Term).
         This includes keywords like "fun", "match", "with" etc.
         when they appear as atoms. */
      Ok(MTerm)
    }

  /* String literal */
  | StringLit(_) => Ok(MString)

  /* Hole — in expression position, this is an OL hole, type Term */
  | Hole(_) => Ok(MTerm)

  /* Application: f x y z — could be ML function application or OL term application */
  | Ap(f, args) =>
    switch (inferExpr(env, f)) {
    | Err(_) as e => e
    | Ok(funTy) =>
      List.fold_left(
        (accResult, arg) =>
          switch (accResult) {
          | Err(_) as e => e
          | Ok(MArrow(paramTy, retTy)) =>
            switch (checkExpr(env, paramTy, arg)) {
            | Err(_) as e => e
            | Ok () => Ok(retTy)
            }
          | Ok(MTerm) =>
            /* OL application: f is a Term, args are Terms, result is Term */
            switch (checkExpr(env, MTerm, arg)) {
            | Err(_) as e => e
            | Ok () => Ok(MTerm)
            }
          | Ok(ty) =>
            err("Cannot apply value of type " ++ printType(ty), f)
          },
        Ok(funTy),
        args,
      )
    }

  /* Type ascription: expr : type — check expr against the declared type.
     In ML context this is a type annotation. */
  | Asc(expr, _typeExpr) =>
    /* TODO: parse the type expression into an mlType and check against it.
       For now, just infer the expression. */
    inferExpr(env, expr)

  /* Arrow: A -> B — this is a type expression, not a value.
     In ML context it appears in type annotations. */
  | Arrow(_, _) => Ok(MSort) /* type expressions have type Sort */

  /* Equals: name = body (used in schema definitions) */
  | Eq(_name, body) => inferExpr(env, body)

  /* Fat arrow: pat => body (lambda or match branch) */
  | FatArrow(_, _) =>
    /* Without expected type info, we can't infer the parameter type.
       This should normally be checked, not inferred. */
    unimpl("Cannot infer type of => without context", t)

  /* Comma: (a, b) — pair */
  | Comma(left, right) =>
    switch (inferExpr(env, left)) {
    | Err(_) as e => e
    | Ok(tyA) =>
      switch (inferExpr(env, right)) {
      | Err(_) as e => e
      | Ok(tyB) => Ok(MPair(tyA, tyB))
      }
    }

  /* Pipe: a | b — used in match branches */
  | Pipe(left, right) =>
    /* Each side of | should be a branch (pat => body) with the same result type */
    switch (inferExpr(env, left)) {
    | Err(_) as e => e
    | Ok(ty) =>
      switch (checkExpr(env, ty, right)) {
      | Err(_) as e => e
      | Ok () => Ok(ty)
      }
    }

  /* List literal */
  | List([]) =>
    /* HACK: empty list — can't infer element type.
       Default to List(Term). TODO: polymorphism */
    Ok(MList(MTerm))
  | List([first, ...rest]) =>
    switch (inferExpr(env, first)) {
    | Err(_) as e => e
    | Ok(elemTy) =>
      let checkResult =
        List.fold_left(
          (acc, item) =>
            switch (acc) {
            | Err(_) as e => e
            | Ok () => checkExpr(env, elemTy, item)
            },
          Ok(),
          rest,
        );
      switch (checkResult) {
      | Err(_) as e => e
      | Ok () => Ok(MList(elemTy))
      };
    }

  /* Postulate block — returns bindings, type is unit-like. Treat as Term for now. */
  | Postulate(_, _) => Ok(MTerm)
  | Schema(_) => Ok(MTerm)
  | Construct(_, _, _) => Ok(MTerm)

  /* BinOp: generic binary operator */
  | BinOp(op, left, right) =>
    switch (op) {
    | "!=" | "==" =>
      switch (inferExpr(env, left)) {
      | Err(_) as e => e
      | Ok(ty) =>
        switch (checkExpr(env, ty, right)) {
        | Err(_) as e => e
        /* HACK: comparison returns... what? No Bool type yet. Use Term. TODO */
        | Ok () => Ok(MTerm)
        }
      }
    | "&&" | "||" =>
      /* HACK: boolean ops on Terms. TODO: add Bool type */
      switch (checkExpr(env, MTerm, left)) {
      | Err(_) as e => e
      | Ok () =>
        switch (checkExpr(env, MTerm, right)) {
        | Err(_) as e => e
        | Ok () => Ok(MTerm)
        }
      }
    | _ =>
      /* Unknown operator — treat as OL application */
      switch (checkExpr(env, MTerm, left)) {
      | Err(_) as e => e
      | Ok () =>
        switch (checkExpr(env, MTerm, right)) {
        | Err(_) as e => e
        | Ok () => Ok(MTerm)
        }
      }
    }

  | Shard(_) | BuilderError => err("Invalid expression", t)
  }

/* --- Check expression against expected type --- */

and checkExpr = (env: mlEnv, expected: mlType, t: term): mlResult(unit) =>
  switch (t.value) {
  /* FatArrow: fun pat => body or bare pat => body (match branch) */
  | FatArrow(lhs, body) =>
    let pat =
      switch (lhs.value) {
      | Ap({value: Identifier("fun"), _}, [p]) => p
      | _ => lhs
      };
    switch (expected) {
    | MArrow(paramTy, retTy) =>
      switch (checkPat(env, paramTy, pat)) {
      | Err(_) as e => e
      | Ok(patEnv) => checkExpr(patEnv, retTy, body)
      }
    | _ => err("=> expression but expected " ++ printType(expected), t)
    }

  /* Ok expr — HACK: polymorphic, Result(t) for any t.
     TODO: replace with principled polymorphism */
  | Ap({value: Identifier("Ok"), _}, [arg]) =>
    switch (expected) {
    | MResult(innerTy) => checkExpr(env, innerTy, arg)
    | _ => err("Ok but expected " ++ printType(expected), t)
    }

  /* Error msg — HACK: polymorphic, Result(t) for any t.
     TODO: replace with principled polymorphism */
  | Ap({value: Identifier("Error"), _}, [arg]) =>
    switch (expected) {
    | MResult(_) => checkExpr(env, MString, arg)
    | _ => err("Error but expected " ++ printType(expected), t)
    }

  /* match s with branches — Ap(match, [scrutinee, with, branch1, branch2, ...]) */
  | Ap({value: Identifier("match"), _}, args) =>
    switch (args) {
    | [scrutinee, {value: Identifier("with"), _}, ...branches] =>
      switch (inferExpr(env, scrutinee)) {
      | Err(_) as e => e
      | Ok(scrutTy) => checkBranches(env, scrutTy, expected, branches)
      }
    | _ => err("Malformed match expression", t)
    }

  /* if cond then thenBr else elseBr — parsed as Ap(if, [cond, then, thenBr, else, elseBr]) */
  | Ap({value: Identifier("if"), _}, args) =>
    let splitIf = (remaining) =>
      switch (remaining) {
      | [cond, {value: Identifier("then"), _}, ...afterThen] =>
        let rec splitElse = (thenAcc, rem) =>
          switch (rem) {
          | [{value: Identifier("else"), _}, ...elseArgs] => Some((cond, thenAcc, elseArgs))
          | [x, ...rest] => splitElse(thenAcc @ [x], rest)
          | [] => Some((cond, thenAcc, []))
          };
        splitElse([], afterThen);
      | _ => None
      };
    switch (splitIf(args)) {
    | Some((_cond, thenArgs, elseArgs)) =>
      let thenBr = combineArgs(thenArgs);
      let elseBr = combineArgs(elseArgs);
      switch (checkExpr(env, expected, thenBr)) {
      | Err(_) as e => e
      | Ok () => checkExpr(env, expected, elseBr)
      }
    | None => err("Malformed if expression", t)
    }

  /* List literal checked against List(t) */
  | List(items) =>
    switch (expected) {
    | MList(elemTy) =>
      List.fold_left(
        (acc, item) =>
          switch (acc) {
          | Err(_) as e => e
          | Ok () => checkExpr(env, elemTy, item)
          },
        Ok(),
        items,
      )
    | _ =>
      /* Fall through to infer */
      switch (inferExpr(env, t)) {
      | Err(_) as e => e
      | Ok(got) => expectType(expected, got, t)
      }
    }

  /* Default: infer and compare */
  | _ =>
    switch (inferExpr(env, t)) {
    | Err(_) as e => e
    | Ok(got) => expectType(expected, got, t)
    }
  }

/* --- Check match branches: pipe-separated pat => body --- */

and checkBranches = (env, scrutTy, expected, branches): mlResult(unit) =>
  /* branches is a list but usually just one element containing the pipe chain */
  List.fold_left(
    (acc, branch) =>
      switch (acc) {
      | Err(_) as e => e
      | Ok () => checkBranch(env, scrutTy, expected, branch)
      },
    Ok(),
    branches,
  )

and checkBranch = (env, scrutTy, expected, t): mlResult(unit) =>
  switch (t.value) {
  | Pipe(left, right) =>
    let leftResult =
      switch (left.value) {
      | Hole(true) => Ok() /* leading | with nothing before it */
      | _ => checkBranch(env, scrutTy, expected, left)
      };
    switch (leftResult) {
    | Err(_) as e => e
    | Ok () => checkBranch(env, scrutTy, expected, right)
    }
  | FatArrow(pat, body) =>
    /* Leading | produces Pipe(Hole(inserted), realPat) — unwrap it */
    let realPat =
      switch (pat.value) {
      | Pipe({value: Hole(true), _}, p) => p
      | _ => pat
      };
    switch (checkPat(env, scrutTy, realPat)) {
    | Err(_) as e => e
    | Ok(patEnv) => checkExpr(patEnv, expected, body)
    }
  | _ =>
    /* Single expression without pattern — check against expected */
    checkExpr(env, expected, t)
  }

/* --- Top-level: check a schema definition --- */

/* Signature = (List (String, Term), Term) */
let signatureType = MPair(MList(MPair(MString, MTerm)), MTerm);

/* Schema type: List Signature -> Result (List Term) */
let schemaType = MArrow(MList(signatureType), MResult(MList(MTerm)));

let checkSchema = (env: mlEnv, body: term): mlResult(unit) =>
  checkExpr(env, schemaType, body);
