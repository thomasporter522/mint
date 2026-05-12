/* ML interpreter for the meta-language.
   Evaluates schema bodies applied to construct declarations.
   Values are ml terms, except closures which capture their environment. */

open Term;

module StringMap = Map.Make(String);

let mk = Term.mkML;

/* --- Value representation --- */

type mlValue =
  | Val(ml)
  | Closure(ref(evalEnv), pat, ml)  /* env (ref for recursion knot-tying), pattern, body */
and evalEnv = StringMap.t(mlValue);

type evalResult =
  | Ok(mlValue)
  | Err(string);

/* --- Structural equality on ml terms --- */

let rec termEqual = (a: ml, b: ml): bool =>
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
  | (Tuple(a), Tuple(b)) =>
    List.length(a) == List.length(b)
    && List.for_all2(termEqual, a, b)
  | (Cons(h1, t1), Cons(h2, t2)) =>
    termEqual(h1, h2) && termEqual(t1, t2)
  | (Hole(_), Hole(_)) => true
  | _ => false
  };

let mlValueEqual = (a: mlValue, b: mlValue): bool =>
  switch (a, b) {
  | (Val(t1), Val(t2)) => termEqual(t1, t2)
  | _ => false
  };

/* --- Extract ml term from mlValue --- */

let termOf = (v: mlValue): ml =>
  switch (v) {
  | Val(t) => t
  | Closure(_, _, _) => mk(Identifier("<closure>"))
  };

/* --- Pattern matching --- */

let rec matchPat = (bindings: evalEnv, p: pat, value: mlValue): option(evalEnv) =>
  switch (p.value) {
  | PWildcard => Some(bindings)

  | PHole => Some(bindings)

  | PVar(name) =>
    switch (StringMap.find_opt(name, bindings)) {
    | Some(existing) =>
      if (mlValueEqual(existing, value)) { Some(bindings) } else { None }
    | None =>
      Some(StringMap.add(name, value, bindings))
    }

  | PString(s) =>
    switch (value) {
    | Val({value: StringLit(s2), _}) when s == s2 => Some(bindings)
    | _ => None
    }

  | PList(pats) =>
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

  | PCons(headPat, tailPat) =>
    switch (value) {
    | Val({value: List([hd, ...tl]), _}) =>
      switch (matchPat(bindings, headPat, Val(hd))) {
      | None => None
      | Some(b) => matchPat(b, tailPat, Val(mk(List(tl))))
      }
    | _ => None
    }

  | PTuple(pats) =>
    switch (value) {
    | Val({value: Tuple(vals), _}) when List.length(pats) == List.length(vals) =>
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

  | PAp(headPat, argPats) =>
    switch (value) {
    | Val({value: Ap(vF, vArgs), _})
        when List.length(argPats) == List.length(vArgs) =>
      switch (matchPat(bindings, headPat, Val(vF))) {
      | None => None
      | Some(b) =>
        List.fold_left2(
          (acc, p, v) =>
            switch (acc) {
            | None => None
            | Some(b) => matchPat(b, p, Val(v))
            },
          Some(b),
          argPats,
          vArgs,
        )
      }
    | _ => None
    }
  };

/* --- Expression evaluation --- */

let rec evalExpr = (env: evalEnv, t: ml): evalResult =>
  switch (t.value) {
  | Identifier(name) =>
    switch (StringMap.find_opt(name, env)) {
    | Some(v) => Ok(v)
    | None => Ok(Val(t))  /* OL identifier, pass through */
    }

  | StringLit(_) => Ok(Val(t))

  | Hole(_) => Ok(Val(t))

  | List(items) => evalList(env, items)

  | Cons(head, tail) =>
    switch (evalExpr(env, head)) {
    | Err(_) as e => e
    | Ok(headVal) =>
      switch (evalExpr(env, tail)) {
      | Err(_) as e => e
      | Ok(Val({value: List(tailVals), _})) =>
        Ok(Val(mk(List([termOf(headVal), ...tailVals]))))
      | Ok(v) => Err("Cons tail is not a list: " ++ Print.printML(termOf(v)))
      }
    }

  | Tuple(items) =>
    let rec evalItems = (acc, remaining) =>
      switch (remaining) {
      | [] =>
        let t = mk(Tuple(List.rev(acc)));
        Ok(Val({...t, meta: {...t.meta, parens: true}}))
      | [item, ...rest] =>
        switch (evalExpr(env, item)) {
        | Err(_) as e => e
        | Ok(v) => evalItems([termOf(v), ...acc], rest)
        }
      };
    evalItems([], items)

  | Fun(pats, body) =>
    switch (pats) {
    | [] => evalExpr(env, body)
    | [pat] => Ok(Closure(ref(env), pat, body))
    | [pat, ...restPats] =>
      /* Multi-param: fun p1 p2 => body  becomes  Closure(env, p1, fun p2 => body) */
      Ok(Closure(ref(env), pat, mk(Fun(restPats, body))))
    }

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
    switch (evalExpr(env, binding.rhs)) {
    | Err(_) as e => e
    | Ok(rhsVal) =>
      let pat = Term.mkPat(PVar(binding.name));
      switch (matchPat(StringMap.empty, pat, rhsVal)) {
      | Some(bindings) =>
        let bodyEnv = StringMap.union((_, _, v) => Some(v), env, bindings);
        evalExpr(bodyEnv, body);
      | None => Err("Let pattern match failed")
      }
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

  | Asc(_, _) => Err("Cannot evaluate ascription")

  | Shard(_) | BuilderError => Err("Cannot evaluate syntax error")
  }

and evalList = (env: evalEnv, items: list(ml)): evalResult => {
  let rec go = (acc: list(ml), remaining: list(ml)): evalResult =>
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

and evalApp = (env: evalEnv, fVal: mlValue, args: list(ml)): evalResult =>
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
    | Ok(Val({value: Tuple([first, ..._]), _})) => Ok(Val(first))
    | Ok(_) => Err("fst: argument is not a tuple")
    }
  | (Val({value: Identifier("snd"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(Val({value: Tuple([_, second, ..._]), _})) => Ok(Val(second))
    | Ok(_) => Err("snd: argument is not a tuple")
    }
  /* apply head args — build Ap(head-term, args) with variadic arity */
  | (Val({value: Identifier("apply"), _}), [headArg, argsArg]) =>
    switch (evalExpr(env, headArg)) {
    | Err(_) as e => e
    | Ok(headVal) =>
      switch (evalExpr(env, argsArg)) {
      | Err(_) as e => e
      | Ok(Val({value: List(items), _})) =>
        Ok(Val(mk(Ap(termOf(headVal), items))))
      | Ok(_) => Err("apply: second argument must be a list")
      }
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

and evalMatch = (env: evalEnv, scrutVal: mlValue, branches: list((pat, ml))): evalResult =>
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

and evalBinOp = (op: binOp, lv: mlValue, rv: mlValue): evalResult =>
  switch (op) {
  | Eq =>
    Ok(Val(mk(Identifier(mlValueEqual(lv, rv) ? "true" : "false"))))
  | Neq =>
    Ok(Val(mk(Identifier(mlValueEqual(lv, rv) ? "false" : "true"))))
  | And =>
    switch (lv, rv) {
    | (Val({value: Identifier("true"), _}), Val({value: Identifier("true"), _})) =>
      Ok(Val(mk(Identifier("true"))))
    | _ => Ok(Val(mk(Identifier("false"))))
    }
  | Or =>
    switch (lv) {
    | Val({value: Identifier("true"), _}) => Ok(Val(mk(Identifier("true"))))
    | _ => Ok(rv)
    }
  };

/* === Top-level: run a schema on construct declarations === */

let declToSignature = (d: decl): ml => {
  let name = mk(Identifier(d.declName));
  let params =
    List.map(
      (p: param) =>
        mk(Tuple([mk(Identifier(p.paramName)), embedOL(p.paramType)])),
      d.params,
    );
  mk(Tuple([name, mk(List(params)), embedOL(d.retType)]));
};

type schemaResult =
  | Witnesses(list(ml))
  | SchemaError(string);

/* Apply a closure value to a single argument. Returns the resulting
   mlValue (which may itself be another closure for a curried function). */
let applyClosure =
    (clos: mlValue, arg: ml): result(mlValue, string) =>
  switch (clos) {
  | Closure(envRef, pat, body) =>
    switch (matchPat(StringMap.empty, pat, Val(arg))) {
    | None => Error("Schema pattern match failed")
    | Some(bindings) =>
      let env = StringMap.union((_, _, v) => Some(v), envRef^, bindings);
      switch (evalExpr(env, body)) {
      | Err(msg) => Error(msg)
      | Ok(v) => Ok(v)
      };
    }
  | Val(_) => Error("Schema is not a function")
  };

let runSchema =
    (schemaVal: mlValue, outerSigs: list(ml), decls: list(decl))
    : schemaResult => {
  let blockSigs = List.map(declToSignature, decls);
  let outerSigList = mk(List(outerSigs));
  let blockSigList = mk(List(blockSigs));
  /* Curried application: schemaVal outer block. */
  switch (applyClosure(schemaVal, outerSigList)) {
  | Error(msg) => SchemaError(msg)
  | Ok(inner) =>
    switch (applyClosure(inner, blockSigList)) {
    | Error(msg) => SchemaError("Schema evaluation error: " ++ msg)
    | Ok(Val({value: Ap({value: Identifier("Ok"), _}, [{value: List(witnesses), _}]), _})) =>
      Witnesses(witnesses)
    | Ok(Val({value: Ap({value: Identifier("Error"), _}, [{value: StringLit(msg), _}]), _})) =>
      SchemaError(msg)
    | Ok(_) => SchemaError("Schema returned invalid result")
    };
  };
};
