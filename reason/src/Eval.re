/* ML interpreter for the meta-language.
   Evaluates schema bodies applied to construct declarations.
   Values are terms, except closures which capture their environment. */

open Term;

module StringMap = Map.Make(String);

/* --- Value representation --- */

type mlValue =
  | Val(term)
  | Closure(ref(evalEnv), term, term)  /* env (ref for recursion knot-tying), pattern, body */
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
    Ok(Closure(ref(env), pat, body))

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

and evalApp = (env: evalEnv, fVal: mlValue, args: list(term)): evalResult =>
  switch (fVal, args) {
  | (Closure(closureEnv, pat, body), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(argVal) =>
      switch (matchPat(StringMap.empty, pat, argVal)) {
      | Some(bindings) =>
        let bodyEnv = StringMap.union((_, _, v) => Some(v), closureEnv^, bindings);
        evalExpr(bodyEnv, body);
      | None => Err("Pattern match failed in function application")
      }
    }
  | (Closure(_), [firstArg, ...restArgs]) =>
    /* Curried: apply first arg, then apply result to rest */
    switch (evalApp(env, fVal, [firstArg])) {
    | Err(_) as e => e
    | Ok(result) => evalApp(env, result, restArgs)
    }
  | (Closure(_), []) => Ok(fVal)
  | (Val({value: Identifier("Ok"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(argVal) => Ok(Val(mk(Ap(mk(Identifier("Ok")), [termOf(argVal)]))))
    }
  | (Val({value: Identifier("Error"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(argVal) => Ok(Val(mk(Ap(mk(Identifier("Error")), [termOf(argVal)]))))
    }
  /* fst and snd — built-in pair projections */
  | (Val({value: Identifier("fst"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(Val({value: Comma(l, _), _})) => Ok(Val(l))
    | Ok(_) => Err("fst: argument is not a pair")
    }
  | (Val({value: Identifier("snd"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(Val({value: Comma(_, r), _})) => Ok(Val(r))
    | Ok(_) => Err("snd: argument is not a pair")
    }
  /* foldl f init list — built-in left fold (curried: f acc item) */
  | (Val({value: Identifier("foldl"), _}), [fArg, initArg, listArg]) =>
    switch (evalExpr(env, fArg)) {
    | Err(_) as e => e
    | Ok(fVal) =>
      switch (evalExpr(env, initArg)) {
      | Err(_) as e => e
      | Ok(initVal) =>
        switch (evalExpr(env, listArg)) {
        | Err(_) as e => e
        | Ok(Val({value: List(items), _})) =>
          List.fold_left(
            (accResult, item) =>
              switch (accResult) {
              | Err(_) as e => e
              | Ok(acc) =>
                /* Apply f to acc, then apply result to item (curried) */
                switch (evalApp(env, fVal, [termOf(acc)])) {
                | Err(_) as e => e
                | Ok(partial) =>
                  evalApp(env, partial, [item])
                }
              },
            Ok(initVal),
            items,
          )
        | Ok(_) => Err("foldl: third argument must be a list")
        }
      }
    }
  | (Val(fTerm), _) =>
    /* OL term application: evaluate args, build Ap */
    switch (evalList(env, args)) {
    | Err(_) as e => e
    | Ok(Val({value: List(argVals), _})) =>
      Ok(Val(mk(Ap(fTerm, argVals))))
    | Ok(_) => Err("Internal: evalList returned non-list")
    }
  }

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

let declToSignature = (decl: term): term =>
  switch (decl.value) {
  | Asc(lhs, retType) =>
    /* Name is the bare identifier, params are the typed parameters */
    let name =
      switch (lhs.value) {
      | Identifier(_) => lhs
      | Ap({value: Identifier(_), _} as f, _) => f
      | _ => lhs
      };
    let params =
      switch (lhs.value) {
      | Ap(_, args) =>
        List.map(
          (arg: term) =>
            switch (arg.value) {
            | Asc({value: Identifier(_), _} as pname, pty) =>
              mk(Comma(pname, pty))
            | _ => mk(Comma(mk(Identifier("_")), arg))
            },
          args,
        )
      | _ => []
      };
    mk(Comma(name,
       mk(Comma(mk(List(params)), retType))))
  | _ =>
    mk(Comma(mk(Hole(true)),
       mk(Comma(mk(List([])), mk(Hole(true))))))
  };

type schemaResult =
  | Witnesses(list(term))
  | SchemaError(string);

let runSchema = (schemaVal: mlValue, decls: list(term)): schemaResult => {
  let sigs = List.map(declToSignature, decls);
  let sigListTerm = mk(List(sigs));
  /* Apply the schema closure to the signature list */
  switch (schemaVal) {
  | Closure(closureEnv, pat, body) =>
    let sigList = Val(sigListTerm);
    switch (matchPat(StringMap.empty, pat, sigList)) {
    | Some(bindings) =>
      let bodyEnv = StringMap.union((_, _, v) => Some(v), closureEnv^, bindings);
      switch (evalExpr(bodyEnv, body)) {
      | Ok(Val({value: Ap({value: Identifier("Ok"), _}, [{value: List(witnesses), _}]), _})) =>
        Witnesses(witnesses)
      | Ok(Val({value: Ap({value: Identifier("Error"), _}, [{value: StringLit(msg), _}]), _})) =>
        SchemaError(msg)
      | Ok(_) => SchemaError("Schema returned invalid result")
      | Err(msg) => SchemaError("Schema evaluation error: " ++ msg)
      }
    | None => SchemaError("Schema pattern match failed on signatures")
    }
  | Val(_) => SchemaError("Schema is not a function")
  };
};
