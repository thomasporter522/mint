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

/* Bridge-injected resolver for `canonical(ctx, goal)`. The bridge sets
   this once at startup; if unset (e.g. running in a context with no
   `child_process`) calls evaluate to `Error "canonical not available"`.
   The function receives the evaluated ctx and goal as ml AST values
   and returns the result as an ml AST value — either
   `Ap(Identifier "Ok", [candidate])` or
   `Ap(Identifier "Error", [StringLit msg])`. */
let canonicalCallbackRef: ref(option((ml, ml) => ml)) = ref(None);
let setCanonicalCallback = (cb: (ml, ml) => ml): unit =>
  canonicalCallbackRef := Some(cb);

/* --- Structural equality on ml terms --- */

let rec termEqual = (a: ml, b: ml): bool =>
  switch (a.value, b.value) {
  | (Identifier(x), Identifier(y)) => x == y
  | (StringLit(x), StringLit(y)) => x == y
  | (TagLit(x), TagLit(y)) => x == y
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
      /* A PVar in head position of a PAp pattern is a constructor
         reference (`Ok x`, `(abs-to _)`, `(ap _ _ f a)`): it asserts
         the value's head identifier is literally that name, and never
         binds. Without this, every PAp would match every Ap of the
         right arity, making `Ok x` and `Error msg` indistinguishable
         and OL postulate patterns like `(abs-to _)` always succeed
         vacuously. Non-PVar heads (e.g. nested PAp) fall through to
         generic matching. */
      switch (headPat.value, vF.value) {
      | (PVar(name), Identifier(vname)) =>
        if (name != vname) {
          None;
        } else {
          List.fold_left2(
            (acc, p, v) =>
              switch (acc) {
              | None => None
              | Some(b) => matchPat(b, p, Val(v))
              },
            Some(bindings),
            argPats,
            vArgs,
          );
        }
      | _ =>
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

  | TagLit(_) => Ok(Val(t))

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
      switch (matchPat(StringMap.empty, binding.pat, rhsVal)) {
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
  /* `print` — debug builtin: print the argument's term form to stdout
     and return it unchanged. Useful for inspecting meta-language values
     when tracing the conversion procedure. Two arg forms supported:
     `(print x)` prints x and returns x; `(print label x)` prefixes a
     label string. */
  | (Val({value: Identifier("print"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(argVal) =>
      print_endline("[print] " ++ Print.printML(termOf(argVal)));
      Ok(argVal);
    }
  | (Val({value: Identifier("print"), _}), [labelArg, arg]) =>
    switch (evalExpr(env, labelArg)) {
    | Err(_) as e => e
    | Ok(labelVal) =>
      switch (evalExpr(env, arg)) {
      | Err(_) as e => e
      | Ok(argVal) =>
        let label =
          switch (termOf(labelVal).value) {
          | StringLit(s) => s
          | _ => Print.printML(termOf(labelVal))
          };
        print_endline("[print] " ++ label ++ ": " ++ Print.printML(termOf(argVal)));
        Ok(argVal);
      }
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
  /* decompose t — view a term as (head, args). For an Ap returns the
     literal pair; for any atomic OL value (Identifier, Hole, Meta)
     returns (t, []). Lets a procedure walk arbitrary terms structurally
     without baking in a fixed pattern at write-time. */
  | (Val({value: Identifier("decompose"), _}), [arg]) =>
    switch (evalExpr(env, arg)) {
    | Err(_) as e => e
    | Ok(Val({value: Ap(f, args), _}) as v) =>
      let parens = termOf(v).meta.parens;
      let tup = mk(Tuple([f, mk(List(args))]));
      Ok(Val({...tup, meta: {...tup.meta, parens}}));
    | Ok(Val(t)) =>
      Ok(Val(mk(Tuple([t, mk(List([]))]))))
    | Ok(_) => Err("decompose: argument is not a term")
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
  /* append xs ys — list concatenation. Both args must be lists; we
     don't enforce element-type agreement at runtime (the typechecker
     already did). */
  | (Val({value: Identifier("append"), _}), [xsArg, ysArg]) =>
    switch (evalExpr(env, xsArg)) {
    | Err(_) as e => e
    | Ok(Val({value: List(xs), _})) =>
      switch (evalExpr(env, ysArg)) {
      | Err(_) as e => e
      | Ok(Val({value: List(ys), _})) => Ok(Val(mk(List(xs @ ys))))
      | Ok(_) => Err("append: second argument must be a list")
      }
    | Ok(_) => Err("append: first argument must be a list")
    }
  /* canonical ctx goal — invoke the bridge-registered solver callback
     and lift its returned (Ok|Error) ml term into mlValue. */
  | (Val({value: Identifier("canonical"), _}), [ctxArg, goalArg]) =>
    switch (evalExpr(env, ctxArg)) {
    | Err(_) as e => e
    | Ok(ctxVal) =>
      switch (evalExpr(env, goalArg)) {
      | Err(_) as e => e
      | Ok(goalVal) =>
        switch (canonicalCallbackRef^) {
        | None =>
          Ok(Val(mk(Ap(mk(Identifier("Error")),
                       [mk(StringLit("canonical not available"))]))))
        | Some(cb) =>
          let result = cb(termOf(ctxVal), termOf(goalVal));
          Ok(Val(result));
        }
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

/* declToSignature takes the construct-block's decls. These are
   freshly-introduced names that haven't yet been tag-lined (tag-lines
   appear after the decls inside the block); so the tag list is empty
   here. (Future: if tag-lines target a freshly-introduced name, the
   schema sees them only on the OUTER scope's view, not this fresh
   one. That matches the "target must already be declared" rule.) */
let declToSignature = (d: decl): ml => {
  let name = mk(Identifier(d.declName));
  let params =
    List.map(
      (p: param) =>
        mk(Tuple([mk(Identifier(p.paramName)), embedOL(p.paramType)])),
      d.params,
    );
  mk(Tuple([name, mk(List(params)), embedOL(d.retType), mk(List([]))]));
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

type coerceResult =
  | Coerced(ml)         /* the procedure returned (Ok wrappedTerm) */
  | CoerceFailed(string) /* (Error msg), or evaluator error, or shape mismatch */
;

/* Run a coerce procedure: schemaVal outerSigs expected found contents.
   Returns Coerced(t) if the procedure produced (Ok t); otherwise CoerceFailed. */
let runCoerce =
    (coerceVal: mlValue, outerSigs: list(ml),
     expected: Term.ol, found: Term.ol, contents: Term.ol)
    : coerceResult => {
  let outerSigList = mk(List(outerSigs));
  let argChain = [outerSigList, embedOL(expected), embedOL(found), embedOL(contents)];
  let rec apply = (clos: mlValue, args: list(ml)): result(mlValue, string) =>
    switch (args) {
    | [] => Ok(clos)
    | [a, ...rest] =>
      switch (applyClosure(clos, a)) {
      | Error(msg) => Error(msg)
      | Ok(next) => apply(next, rest)
      }
    };
  switch (apply(coerceVal, argChain)) {
  | Error(msg) => CoerceFailed("Coerce evaluation error: " ++ msg)
  | Ok(Val({value: Ap({value: Identifier("Ok"), _}, [t]), _})) => Coerced(t)
  | Ok(Val({value: Ap({value: Identifier("Error"), _}, [{value: StringLit(msg), _}]), _})) =>
    CoerceFailed(msg)
  | Ok(_) => CoerceFailed("Coerce returned invalid result")
  };
};
