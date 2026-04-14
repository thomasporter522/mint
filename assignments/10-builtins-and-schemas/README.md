# Assignment 10: Builtins and Schemas

## Overview

Implement function application, built-in functions, and the schema execution
pipeline. This completes the evaluator: after this assignment, schemas can
process construct declarations and produce witness terms.

The core evaluator (evalExpr, matchPat, evalBinOp, etc.) is already complete
from assignment 9. This assignment adds `evalApp`, `declToSignature`, and
`runSchema`.

## Key concepts

### Function application (evalApp)

`evalApp(env, fVal, args)` applies a function value to a list of argument
terms. The function value is already evaluated; the arguments are unevaluated
terms that evalApp must evaluate.

There are several cases:

**Closure application (single arg):** Match the closure's pattern against the
evaluated argument. On success, evaluate the body in the closure's environment
extended with the pattern bindings.

**Closure application (curried multi-arg):** When a closure receives multiple
arguments, apply the first argument to get a result, then apply that result
to the remaining arguments. This is how curried functions like
`fun x => fun y => ...` work when called as `f a b`.

**Closure application (zero args):** Return the closure unchanged.

**Ok/Error constructors:** `Ok expr` and `Error expr` evaluate the argument
and wrap it in an application node: `Ap(Identifier("Ok"), [evaluated_arg])`.
These are how schemas report success or failure.

**fst/snd pair projections:** `fst (a, b)` returns `a`, `snd (a, b)` returns
`b`. The argument must evaluate to a Comma value.

**foldl — curried left fold:** `foldl f init list` takes three arguments.
The callback `f` is curried: it receives the accumulator first, then the item.
So the fold applies `f` to the accumulator to get a partial function, then
applies that partial function to the current item.

Example: `foldl (fun acc => fun item => acc) init [a, b, c]`
- Step 1: apply f to init, get partial; apply partial to a
- Step 2: apply f to result, get partial; apply partial to b
- Step 3: apply f to result, get partial; apply partial to c

This is the standard curried fold. Schemas use foldl to build up OL terms
from lists of declarations (e.g., reconstructing `(f x y)` from the name `f`
and params `[x, y]`).

**OL term application (fallback):** When the function is a Val (not a closure
or builtin), evaluate all arguments and build an Ap node. This is how schemas
construct OL terms like `(eq A A a a)` — `eq` is an OL identifier (Val), and
the args are evaluated and assembled into an application.

### Schema execution pipeline

Schemas are closures that receive a list of signatures and return a Result.

**declToSignature(decl):** Converts a construct declaration (an Asc node) into
a signature triple `(name, (params, retType))` represented as nested Comma/List:

- The name is the bare identifier (not the applied form)
- Params is a list of `(paramName, paramType)` pairs
- retType is the return type

For `(f (x : A) (y : B)) : T`, the signature is:
`(f, ([x, A), (y, B)], T))`

For a bare `c : T` with no params, the signature is:
`(c, ([], T))`

For malformed declarations, return `(?, ([], ?))`.

**runSchema(schemaVal, decls):** Applies a schema closure to construct
declarations:

1. Convert each declaration to a signature via declToSignature
2. Wrap the signatures in a list term
3. Apply the schema closure to the list (pattern match + eval body)
4. Inspect the result:
   - `Ok([witnesses])` — extract the witness list
   - `Error("msg")` — extract the error message
   - Anything else — schema returned invalid result

## What to implement

### evalApp — all cases

- **Closure, single arg** — eval arg, matchPat, eval body in extended env
- **Closure, multiple args** — apply first arg, then apply result to rest (curried)
- **Closure, zero args** — return closure unchanged
- **Ok constructor** — eval arg, wrap in Ap(Identifier("Ok"), [result])
- **Error constructor** — eval arg, wrap in Ap(Identifier("Error"), [result])
- **fst** — eval arg, extract left of Comma
- **snd** — eval arg, extract right of Comma
- **foldl** — eval all three args; fold over list items with curried callback
- **Val (OL term)** — eval args via evalList, build Ap node

### declToSignature

Convert an Asc declaration to a `(name, (params, retType))` triple.
Handle both parameterized `(f (x:A) (y:B)) : T` and bare `c : T` forms.

### runSchema

Apply schema closure to signature list, pattern-match the Result output.

## Tests

```bash
make reason
make test
```
