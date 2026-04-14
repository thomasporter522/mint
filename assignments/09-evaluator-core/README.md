# Assignment 9: Evaluator Core

## Overview

Implement the core ML expression evaluator. The meta-language evaluates
expressions in `meta` blocks: schema bodies, let definitions, and helper
functions. Values are either OL terms (passed through as data) or closures
(which capture their environment).

Read `Term.re` for the AST and `Print.re` for the printer before starting.
The evaluator lives in `Eval.re`.

## Key concepts

### Values

There are two kinds of ML value:

- **Val(term)** — an object-language term used as a value. Identifiers not
  bound in the ML environment pass through as OL terms. Lists, pairs, strings,
  and applications all evaluate to Val-wrapped terms.
- **Closure(env, pat, body)** — a function closure. `fun pat => body` captures
  the current environment. When applied, the pattern is matched against the
  argument and the body is evaluated in the closure's environment extended
  with the pattern bindings.

### Evaluation model

`evalExpr(env, term)` returns `evalResult = Ok(mlValue) | Err(string)`.

Every case either produces a value or propagates an error. The pattern
throughout is: evaluate sub-expressions, check for errors, combine results.

Identifiers not found in the environment are treated as OL identifiers and
returned as `Val(Identifier(name))`. This is how schemas manipulate OL terms:
names like `eq`, `refl`, `Nat` are not ML bindings, so they pass through as
term values that can be assembled into OL expressions.

### Pattern matching

`matchPat(bindings, pat, value)` returns `option(evalEnv)`. It attempts to
match a value against a pattern, extending the bindings map on success.

Patterns support nonlinear matching: the first occurrence of an identifier
binds it; subsequent occurrences of the same identifier require equality
with the already-bound value (checked via `mlValueEqual`).

## What to implement

### Structural equality

- **termEqual(a, b)** — recursive structural equality on AST terms. Compare
  Identifier, StringLit, Ap (head + args), List, Comma, Arrow, Asc, Hole.
  All other cases return false.
- **mlValueEqual(a, b)** — equality on values. Two Val values are equal if
  their terms are structurally equal. Closures are never equal.
- **termOf(v)** — extract the term from a value. Closures become
  `Identifier("<closure>")`.

### Pattern matching (matchPat)

All pattern cases:

- **Identifier("_")** — wildcard, always matches, binds nothing
- **Hole(_)** — wildcard, always matches, binds nothing
- **Identifier(name)** — if name is already bound, check equality (nonlinear);
  otherwise bind name to the value
- **StringLit(s)** — match against Val(StringLit(s2)) when s == s2
- **List(pats)** — match against Val(List(vals)) when lengths match; match
  each element pairwise
- **Cons(headPats, tailPat)** — match against Val(List(vals)) when there are
  enough elements; match head elements pairwise, then match tailPat against
  the remaining elements as a list
- **Comma(pL, pR)** — match against Val(Comma(vL, vR)); match each side
- **Ap(pF, pArgs)** — match against Val(Ap(vF, vArgs)) when arg counts match;
  match the function head, then match each arg pairwise
- All other patterns: return None

### Expression evaluation (evalExpr)

Implement all cases:

- **Identifier(name)** — look up in env; if not found, return as OL term
- **StringLit** — return as Val
- **Hole** — return as Val
- **List(items)** — evaluate each item via evalList
- **Cons(heads, tail)** — evaluate heads and tail, concatenate the lists
- **Comma(left, right)** — evaluate both sides, build a Comma val with
  parens=true in the meta
- **Fun(pat, body)** — return a Closure capturing the current env
- **Ap(f, args)** — evaluate f, then delegate to evalApp (leave as TODO
  in this assignment)
- **Match(scrut, branches)** — evaluate scrutinee, then delegate to evalMatch
- **If(cond, then, else)** — evaluate condition; if it's Identifier("true")
  evaluate the then branch, if Identifier("false") evaluate else, otherwise error
- **Let(binding, body)** — binding must be an Eq(pat, expr); evaluate expr,
  match pat, evaluate body in extended env
- **BinOp(op, left, right)** — evaluate both sides, delegate to evalBinOp
- **Asc(expr, _)** — evaluate the expression, ignore the type annotation
- **Eq(_, body)** — evaluate the body (the right side of `=`)
- **Arrow(a, b)** — evaluate both sides, build an Arrow val
- **Postulate/Meta/Construct** — error: cannot evaluate blocks in ML
- **Shard/BuilderError** — error: cannot evaluate syntax errors

### List evaluation (evalList)

Evaluate a list of terms to a `Val(List(...))`. Accumulate evaluated terms
in reverse, then reverse at the end.

### Match dispatch (evalMatch)

Try each branch in order. For each (pat, body) pair, attempt matchPat with
empty initial bindings. On first successful match, evaluate the body in env
extended with the pattern bindings. If no branch matches, return
"Non-exhaustive match" error.

### Binary operators (evalBinOp)

- **==** — return Identifier("true") or Identifier("false") based on mlValueEqual
- **!=** — the inverse of ==
- **&&** — true only if both sides are Identifier("true")
- **||** — if left is Identifier("true"), return true; otherwise return the right value

### Not in this assignment

Leave `evalApp` as a stub that returns `failwith("TODO: evalApp")`.
The builtin functions (foldl, fst, snd), constructors (Ok, Error),
closure application, and OL term application are covered in assignment 10.

## Tests

```bash
make reason
make test
```
