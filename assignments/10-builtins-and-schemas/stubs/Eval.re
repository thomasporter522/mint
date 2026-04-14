/* ML interpreter for the meta-language.
   Evaluates schema bodies applied to construct declarations.
   Values are terms, except closures which capture their environment. */

open Term;

module StringMap = Map.Make(String);

/* --- Value representation --- */

type mlValue =
  | Val(term)
  | Closure(evalEnv, term, term)  /* env, pattern, body */
and evalEnv = StringMap.t(mlValue);

type evalResult =
  | Ok(mlValue)
  | Err(string);

/* --- Structural equality on terms --- */

let rec termEqual = (a: term, b: term): bool =>
  switch (a.value, b.value) {
  | (Identifier(x), Identifier(y)) => x == y
  | (StringLit(x), StringLit(y)) => x == y
  | (Ap(f1, args1), Ap(f2, args2)) =>
    termEqual(f1, f2)
    && List.length(args1) == List.length(args2)
    && List.for_all2(termEqual, args1, args2)
  | (List(a), List(b)) =>
    List.length(a) == List.length(b)
    && List.for_all2(termEqual, a, b)
  | (Comma(a1, b1), Comma(a2, b2)) =>
    termEqual(a1, a2) && termEqual(b1, b2)
  | (Arrow(a1, b1), Arrow(a2, b2)) =>
    termEqual(a1, a2) && termEqual(b1, b2)
  | (Asc(a1, b1), Asc(a2, b2)) =>
    termEqual(a1, a2) && termEqual(b1, b2)
  | (Hole(_), Hole(_)) => true
  | _ => false
  };

let mlValueEqual = (a: mlValue, b: mlValue): bool =>
  switch (a, b) {
  | (Val(t1), Val(t2)) => termEqual(t1, t2)
  | _ => false
  };

/* --- Extract term from mlValue --- */

let termOf = (v: mlValue): term =>
  switch (v) {
  | Val(t) => t
  | Closure(_, _, _) => mk(Identifier("<closure>"))
  };

/* --- Pattern matching --- */

let rec matchPat = (bindings: evalEnv, pat: term, value: mlValue): option(evalEnv) =>
  switch (pat.value) {
  | Identifier("_") => Some(bindings)

  | Hole(_) => Some(bindings)

  | Identifier(name) =>
    switch (StringMap.find_opt(name, bindings)) {
    | Some(existing) =>
      if (mlValueEqual(existing, value)) { Some(bindings) } else { None }
    | None =>
      Some(StringMap.add(name, value, bindings))
    }

  | StringLit(s) =>
    switch (value) {
    | Val({value: StringLit(s2), _}) when s == s2 => Some(bindings)
    | _ => None
    }

  | List(pats) =>
    switch (value) {
    | Val({value: List(vals), _}) when List.length(pats) == List.length(vals) =>
      List.fold_left2(
        (acc, p, v) =>
          switch (acc) {
          | None => None
          | Some(b) => matchPat(b, p, Val(v))
          },
        Some(bindings),
        pats,
        vals,
      )
    | _ => None
    }

  | Cons(headPats, tailPat) =>
    switch (value) {
    | Val({value: List(vals), _}) when List.length(vals) >= List.length(headPats) =>
      let headVals = List.filteri((i, _) => i < List.length(headPats), vals);
      let tailVals = List.filteri((i, _) => i >= List.length(headPats), vals);
      let headResult = List.fold_left2(
        (acc, p, v) =>
          switch (acc) {
          | None => None
          | Some(b) => matchPat(b, p, Val(v))
          },
        Some(bindings),
        headPats,
        headVals,
      );
      switch (headResult) {
      | None => None
      | Some(b) => matchPat(b, tailPat, Val(mk(List(tailVals))))
      }
    | _ => None
    }

  | Comma(pL, pR) =>
    switch (value) {
    | Val({value: Comma(vL, vR), _}) =>
      switch (matchPat(bindings, pL, Val(vL))) {
      | None => None
      | Some(b) => matchPat(b, pR, Val(vR))
      }
    | _ => None
    }

  | Ap(pF, pArgs) =>
    switch (value) {
    | Val({value: Ap(vF, vArgs), _}) when List.length(pArgs) == List.length(vArgs) =>
      switch (matchPat(bindings, pF, Val(vF))) {
      | None => None
      | Some(b) =>
        List.fold_left2(
          (acc, p, v) =>
            switch (acc) {
            | None => None
            | Some(b) => matchPat(b, p, Val(v))
            },
          Some(b),
          pArgs,
          vArgs,
        )
      }
    | _ => None
    }

  | _ => None
  };

/* --- Expression evaluation --- */

let rec evalExpr = (env: evalEnv, t: term): evalResult =>
  switch (t.value) {
  | Identifier(name) =>
    switch (StringMap.find_opt(name, env)) {
    | Some(v) => Ok(v)
    | None => Ok(Val(t))  /* OL identifier, pass through */
    }

  | StringLit(_) => Ok(Val(t))

  | Hole(_) => Ok(Val(t))

  | List(items) => evalList(env, items)

  | Cons(heads, tail) =>
    switch (evalList(env, heads)) {
    | Err(_) as e => e
    | Ok(Val({value: List(headVals), _})) =>
      switch (evalExpr(env, tail)) {
      | Err(_) as e => e
      | Ok(Val({value: List(tailVals), _})) =>
        Ok(Val(mk(List(headVals @ tailVals))))
      | Ok(v) => Err("Cons tail is not a list: " ++ Print.printTerm(termOf(v)))
      }
    | Ok(_) => Err("Internal: evalList returned non-list")
    }

  | Comma(left, right) =>
    switch (evalExpr(env, left)) {
    | Err(_) as e => e
    | Ok(lv) =>
      switch (evalExpr(env, right)) {
      | Err(_) as e => e
      | Ok(rv) =>
        let t = mk(Comma(termOf(lv), termOf(rv)));
        Ok(Val({...t, meta: {...t.meta, parens: true}}));
      }
    }

  | Fun(pat, body) =>
    Ok(Closure(env, pat, body))

  | Ap(f, args) =>
    switch (evalExpr(env, f)) {
    | Err(_) as e => e
    | Ok(fVal) => evalApp(env, fVal, args)
    }

  | Match(scrut, branches) =>
    switch (evalExpr(env, scrut)) {
    | Err(_) as e => e
    | Ok(scrutVal) => evalMatch(env, scrutVal, branches)
    }

  | If(cond, thenBr, elseBr) =>
    switch (evalExpr(env, cond)) {
    | Err(_) as e => e
    | Ok(Val({value: Identifier("true"), _})) => evalExpr(env, thenBr)
    | Ok(Val({value: Identifier("false"), _})) => evalExpr(env, elseBr)
    | Ok(_) => Err("if condition is not a boolean")
    }

  | Let(binding, body) =>
    switch (binding.value) {
    | Eq(pat, expr) =>
      switch (evalExpr(env, expr)) {
      | Err(_) as e => e
      | Ok(exprVal) =>
        switch (matchPat(StringMap.empty, pat, exprVal)) {
        | Some(bindings) =>
          let bodyEnv = StringMap.union((_, _, v) => Some(v), env, bindings);
          evalExpr(bodyEnv, body);
        | None => Err("Let pattern match failed")
        }
      }
    | _ => Err("Invalid let binding")
    }

  | BinOp(op, left, right) =>
    switch (evalExpr(env, left)) {
    | Err(_) as e => e
    | Ok(lv) =>
      switch (evalExpr(env, right)) {
      | Err(_) as e => e
      | Ok(rv) => evalBinOp(op, lv, rv)
      }
    }

  | Asc(expr, _) => evalExpr(env, expr)

  | Eq(_, body) => evalExpr(env, body)

  | Arrow(a, b) =>
    switch (evalExpr(env, a)) {
    | Err(_) as e => e
    | Ok(av) =>
      switch (evalExpr(env, b)) {
      | Err(_) as e => e
      | Ok(bv) => Ok(Val(mk(Arrow(termOf(av), termOf(bv)))))
      }
    }

  | Postulate(_, _) | Meta(_, _) | Construct(_, _, _) =>
    Err("Cannot evaluate block in ML expression")

  | Shard(_) | BuilderError => Err("Cannot evaluate syntax error")
  }

and evalList = (env: evalEnv, items: list(term)): evalResult => {
  let rec go = (acc: list(term), remaining: list(term)): evalResult =>
    switch (remaining) {
    | [] => Ok(Val(mk(List(List.rev(acc)))))
    | [item, ...rest] =>
      switch (evalExpr(env, item)) {
      | Err(_) as e => e
      | Ok(v) => go([termOf(v), ...acc], rest)
      }
    };
  go([], items);
}

/* TODO: Implement evalApp — function application with all cases.

   Cases to handle (in this order):

   1. Closure with single arg:
      - Evaluate the argument
      - Match the closure's pattern against the evaluated arg value
      - Evaluate the body in the closure's env extended with pattern bindings
      - Error on pattern match failure

   2. Closure with multiple args (curried):
      - Apply closure to just the first arg (recurse with [firstArg])
      - Apply the result to the remaining args (recurse with restArgs)

   3. Closure with zero args:
      - Return the closure unchanged

   4. Ok constructor — Val(Identifier("Ok")) with one arg:
      - Evaluate the argument
      - Return Val(Ap(Identifier("Ok"), [evaluated_arg]))

   5. Error constructor — Val(Identifier("Error")) with one arg:
      - Evaluate the argument
      - Return Val(Ap(Identifier("Error"), [evaluated_arg]))

   6. fst — Val(Identifier("fst")) with one arg:
      - Evaluate the argument
      - If it's a Comma(l, r), return Val(l)
      - Otherwise error "fst: argument is not a pair"

   7. snd — Val(Identifier("snd")) with one arg:
      - Evaluate the argument
      - If it's a Comma(_, r), return Val(r)
      - Otherwise error "snd: argument is not a pair"

   8. foldl — Val(Identifier("foldl")) with three args [fArg, initArg, listArg]:
      - Evaluate all three arguments
      - listArg must evaluate to a List
      - Fold over the list items using List.fold_left:
        For each item, apply fVal to the accumulator (curried: apply to acc,
        get partial, apply partial to item)
      - Error if third arg is not a list

   9. Val (OL term application, fallback):
      - Evaluate all args via evalList
      - Build Ap(fTerm, argVals)
      - This constructs OL terms like (eq A A a a) */
and evalApp = (_env: evalEnv, _fVal: mlValue, _args: list(term)): evalResult =>
  failwith("TODO: evalApp")

and evalMatch = (env: evalEnv, scrutVal: mlValue, branches: list((term, term))): evalResult =>
  switch (branches) {
  | [] => Err("Non-exhaustive match")
  | [(pat, body), ...rest] =>
    switch (matchPat(StringMap.empty, pat, scrutVal)) {
    | Some(bindings) =>
      let bodyEnv = StringMap.union((_, _, v) => Some(v), env, bindings);
      evalExpr(bodyEnv, body);
    | None => evalMatch(env, scrutVal, rest)
    }
  }

and evalBinOp = (op: string, lv: mlValue, rv: mlValue): evalResult =>
  switch (op) {
  | "==" =>
    Ok(Val(mk(Identifier(mlValueEqual(lv, rv) ? "true" : "false"))))
  | "!=" =>
    Ok(Val(mk(Identifier(mlValueEqual(lv, rv) ? "false" : "true"))))
  | "&&" =>
    switch (lv, rv) {
    | (Val({value: Identifier("true"), _}), Val({value: Identifier("true"), _})) =>
      Ok(Val(mk(Identifier("true"))))
    | _ => Ok(Val(mk(Identifier("false"))))
    }
  | "||" =>
    switch (lv) {
    | Val({value: Identifier("true"), _}) => Ok(Val(mk(Identifier("true"))))
    | _ => Ok(rv)
    }
  | _ => Err("Unknown operator: " ++ op)
  };

/* === Top-level: run a schema on construct declarations === */

/* TODO: Implement declToSignature.
   Convert a construct declaration (an Asc node) into a signature triple
   (name, (params, retType)) represented as nested Comma and List terms.

   For Asc(lhs, retType):
   - Extract name: if lhs is Identifier, use it directly; if lhs is
     Ap(Identifier(_) as f, _), use f; otherwise use lhs as-is
   - Extract params: if lhs is Ap(_, args), map each arg:
     - Asc(Identifier(_) as pname, pty) becomes Comma(pname, pty)
     - Other args become Comma(Identifier("_"), arg)
     If lhs is not Ap, params is empty list
   - Return: Comma(name, Comma(List(params), retType))

   For non-Asc declarations:
   - Return: Comma(Hole(true), Comma(List([]), Hole(true))) */
let declToSignature = (_decl: term): term =>
  failwith("TODO: declToSignature");

type schemaResult =
  | Witnesses(list(term))
  | SchemaError(string);

/* TODO: Implement runSchema.
   Apply a schema closure to construct declarations:

   1. Convert each declaration to a signature via declToSignature
   2. Wrap the signature list in a List term
   3. Apply the schema closure:
      - Match the closure's pattern against Val(sigListTerm)
      - Evaluate the body in the closure's env extended with bindings
   4. Interpret the result:
      - Ok(Val(Ap(Identifier("Ok"), [List(witnesses)]))) => Witnesses(witnesses)
      - Ok(Val(Ap(Identifier("Error"), [StringLit(msg)]))) => SchemaError(msg)
      - Ok(_) => SchemaError("Schema returned invalid result")
      - Err(msg) => SchemaError("Schema evaluation error: " ++ msg)
   5. If pattern match fails: SchemaError("Schema pattern match failed on signatures")
   6. If schemaVal is Val (not closure): SchemaError("Schema is not a function") */
let runSchema = (_schemaVal: mlValue, _decls: list(term)): schemaResult =>
  failwith("TODO: runSchema");
