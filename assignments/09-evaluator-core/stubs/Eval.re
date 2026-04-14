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

/* TODO: Implement recursive structural equality on AST terms.
   Compare the .value of each term. Cases to handle:
   - Identifier(x) vs Identifier(y) — equal when x == y
   - StringLit(x) vs StringLit(y) — equal when x == y
   - Ap(f1, args1) vs Ap(f2, args2) — equal when heads equal, same length, all args equal
   - List(a) vs List(b) — equal when same length and all elements equal
   - Comma(a1, b1) vs Comma(a2, b2) — equal when both sides equal
   - Arrow(a1, b1) vs Arrow(a2, b2) — equal when both sides equal
   - Asc(a1, b1) vs Asc(a2, b2) — equal when both sides equal
   - Hole(_) vs Hole(_) — always equal
   - All other combinations — false */
let termEqual = (_a: term, _b: term): bool =>
  failwith("TODO: termEqual");

/* TODO: Implement equality on mlValues.
   Two Val values are equal if their terms are structurally equal (via termEqual).
   Closures are never equal to anything. */
let mlValueEqual = (_a: mlValue, _b: mlValue): bool =>
  failwith("TODO: mlValueEqual");

/* --- Extract term from mlValue --- */

/* TODO: Extract the term from an mlValue.
   Val(t) => t
   Closure(_, _, _) => mk(Identifier("<closure>")) */
let termOf = (_v: mlValue): term =>
  failwith("TODO: termOf");

/* --- Pattern matching --- */

/* TODO: Implement pattern matching. matchPat(bindings, pat, value) attempts to
   match value against pat, extending bindings on success.

   Pattern cases:
   - Identifier("_") — wildcard, always succeeds, binds nothing
   - Hole(_) — wildcard, always succeeds, binds nothing
   - Identifier(name) — if name already in bindings, check equality (nonlinear);
     otherwise add binding
   - StringLit(s) — match Val(StringLit(s2)) when s == s2
   - List(pats) — match Val(List(vals)) when lengths equal; match pairwise
   - Cons(headPats, tailPat) — match Val(List(vals)) when enough elements;
     match head elements, then match tailPat against remaining as a list
   - Comma(pL, pR) — match Val(Comma(vL, vR)); match each side
   - Ap(pF, pArgs) — match Val(Ap(vF, vArgs)) when arg counts equal;
     match head, then match args pairwise
   - All other patterns — None */
let matchPat = (_bindings: evalEnv, _pat: term, _value: mlValue): option(evalEnv) =>
  failwith("TODO: matchPat");

/* --- Expression evaluation --- */

/* TODO: Implement the expression evaluator.
   Each case evaluates sub-expressions, propagates errors, and combines results.

   Cases:
   - Identifier(name) — look up in env; if not found, return as OL term Val(t)
   - StringLit(_) — return Val(t)
   - Hole(_) — return Val(t)
   - List(items) — delegate to evalList
   - Cons(heads, tail) — evaluate heads via evalList, evaluate tail, concatenate
   - Comma(left, right) — evaluate both, build Comma val with parens=true
   - Fun(pat, body) — return Closure(env, pat, body)
   - Ap(f, args) — evaluate f, then delegate to evalApp
   - Match(scrut, branches) — evaluate scrutinee, delegate to evalMatch
   - If(cond, thenBr, elseBr) — evaluate cond; branch on Identifier("true"/"false")
   - Let(binding, body) — binding is Eq(pat, expr); eval expr, match pat, eval body
   - BinOp(op, left, right) — evaluate both, delegate to evalBinOp
   - Asc(expr, _) — evaluate expr, ignore annotation
   - Eq(_, body) — evaluate body
   - Arrow(a, b) — evaluate both, build Arrow val
   - Postulate/Meta/Construct — error
   - Shard/BuilderError — error */
let rec evalExpr = (_env: evalEnv, _t: term): evalResult =>
  failwith("TODO: evalExpr")

/* TODO: Evaluate a list of terms into Val(List(...)).
   Use a recursive helper that accumulates evaluated terms in reverse,
   then reverses at the end. Propagate errors. */
and evalList = (_env: evalEnv, _items: list(term)): evalResult => {
  ignore(evalExpr);
  failwith("TODO: evalList");
}

/* TODO: evalApp — leave as stub for assignment 10 */
and evalApp = (_env: evalEnv, _fVal: mlValue, _args: list(term)): evalResult => {
  ignore(evalList);
  failwith("TODO: evalApp");
}

/* TODO: Try each branch in order. For each (pat, body):
   - matchPat with empty bindings against scrutVal
   - On success, evaluate body in env extended with pattern bindings
   - On failure, try next branch
   - If no branches match, return "Non-exhaustive match" error */
and evalMatch = (_env: evalEnv, _scrutVal: mlValue, _branches: list((term, term))): evalResult => {
  ignore(evalApp);
  failwith("TODO: evalMatch");
}

/* TODO: Evaluate binary operators.
   - "==" — Identifier("true"/"false") via mlValueEqual
   - "!=" — inverse of ==
   - "&&" — true only when both are Identifier("true")
   - "||" — if left is Identifier("true"), return true; otherwise return right value
   - Unknown operator — error */
and evalBinOp = (_op: string, _lv: mlValue, _rv: mlValue): evalResult => {
  ignore(evalMatch);
  failwith("TODO: evalBinOp");
};

/* === Top-level: run a schema on construct declarations === */

/* Provided — not part of this assignment */

let declToSignature = (decl: term): term =>
  switch (decl.value) {
  | Asc(lhs, retType) =>
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
  switch (schemaVal) {
  | Closure(closureEnv, pat, body) =>
    let sigList = Val(sigListTerm);
    switch (matchPat(StringMap.empty, pat, sigList)) {
    | Some(bindings) =>
      let bodyEnv = StringMap.union((_, _, v) => Some(v), closureEnv, bindings);
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
