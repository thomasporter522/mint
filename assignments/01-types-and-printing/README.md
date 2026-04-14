# Assignment 1: Types and Printing

## Overview

Implement the ML type system representation and the AST pretty printer.
These are small modules that give you familiarity with the core data structures.

Read `Term.re` first — it defines the AST that everything operates on.

## Files to implement

- **MLType.re** — ML type representation, equality, and printing
- **Print.re** — AST pretty printer (printTerm, debugTerm)

## MLType.re

The meta-language has these types:
- `Term` — an object-language term (the base type)
- `Sort` — the type of types
- `Bool` — booleans (true/false)
- `String` — string literals
- `List T` — lists with element type T
- `Result T` — Ok/Error results with payload type T
- `(A, B)` — pairs
- `A -> B` — functions

Implement:
1. `printType` — convert a type to its string representation
2. `printTypeAtom` — like printType but wraps compound types in parens
   (List, Result, Arrow need parens; Term, Sort, Bool, String, Pair don't)
3. `eqType` — structural equality on types

## Print.re

Implement the pretty printer for AST terms. Key cases:
- `Identifier(s)` → `s`
- `StringLit(s)` → `"s"` (with quotes)
- `Hole(false)` → `?` (user-written holes)
- `Hole(true)` → `?` (synthetic holes, same display)
- `Ap(f, args)` → `f a1 a2 ...` (space-separated, wrap in parens if has parens meta)
- `Asc(left, right)` → `left : right` (wrap parens around Asc inside Ap)
- `Arrow(l, r)` → `l -> r`
- `Eq(l, r)` → `l = r`
- `List(items)` → `[a, b, c]`
- `Cons(heads, tail)` → `[h1, h2, ...tail]`
- `Comma(l, r)` → `l, r` (with parens if meta says so)
- `Fun(pat, body)` → `fun pat => body`
- `Match(scrut, branches)` → `match scrut with | p1 => b1 | p2 => b2 end`
- `If(c, t, e)` → `if c then t else e end`
- `Let(binding, body)` → `let binding in body`
- `BinOp(op, l, r)` → `l op r`
- `Postulate(body, rest)` → `postulate\n...`
- `Meta(body, rest)` → `meta\n...`
- `Construct(by, body, rest)` → `construct by ...\n...`

Also implement `debugTerm` which shows the AST structure (for debugging):
- `Id(x)`, `Str("s")`, `Hole`, `Hole_`, `Asc(...)`, `Arrow(...)`, etc.
- Prefix with `P` for nodes with parens=true: `PAp(...)`, `PArrow(...)`, etc.

## Tests

After implementing, these should work:
```bash
# Build
make reason

# Test printing (manually)
make try EXPR='(f x y)'
make debug EXPR='(f x y)'
```

Full parse tests (assignment 5 checkpoint) will exercise printing thoroughly.
