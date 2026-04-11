## Type issues in enum-coprod-generic.mint

The generic enum schema works correctly at runtime (all 3 construct blocks produce
valid witnesses). But the ML type checker reports 8 errors, all from one root cause.

### The issue: lambda parameters infer as Term

In inference mode, `fun x => body` gives `x` type `Term` (the only option without
type annotations or polymorphism). When a MetaLet function like `reverse` is defined:

```
reverse = fun xs => (foldl (fun acc => fun x => [x, ...acc]) [] xs)
-- inferred type: Term -> List Term
```

Calling it with a `List Term` argument produces a type error:

```
(reverse some-list)
-- checks some-list against Term (the param type)
-- some-list : List Term
-- List Term != Term -> error
```

This affects every call to `reverse`, `append`, `concat`, `build-injs-and-type`,
`build-elim`, and `build-proofs` in the schema body.

### All 8 errors

1. `reverse tc-and-scrut` — passing List (Term, Term) as Term
2. `build-injs-and-type rest-case-vars` — passing List Term as Term
3-4. `build-elim mvar case-vars rest-case-vars` — two List Term args as Term
5-6. `build-proofs mvar case-vars rest-case-vars` — two List Term args as Term
7. `concat [[...]]` — passing List (List Term) as Term
8. Result type propagation from concat

### What was fixed (no longer causing errors)

The original split logic accumulated signature-typed entries into `[]`-seeded lists,
causing `List Signature != List Term` mismatches. Replaced with a foldl that finds
the case params by scanning with a properly-seeded accumulator `(false, [(star, star)])`.

### Possible fixes (all require language changes)

1. **Type annotations on let bindings**: `reverse : List Term -> List Term = fun xs => ...`
2. **Polymorphism**: `reverse : forall A. List A -> List A`
3. **Subtyping**: everything is a Term at the value level, so `List Term <: Term`
