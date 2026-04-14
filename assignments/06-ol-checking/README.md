# Assignment 6: OL Checking

## Overview

In this assignment you implement the **Object Language (OL) type checker** for Mint. The OL is the kernel language: a dependently-typed system where declarations introduce fully-applied term constructors with signatures. The only built-in is `Sort` (the kind of types). Everything else -- universes, equality, function application -- is user-declared via postulate blocks.

The checker works by processing declarations in sequence. Each declaration `(name (arg1 : T1) ...) : ReturnType` adds a binding to the context. Subsequent declarations can reference earlier ones. When a term is used in expression position, the checker looks up its type, checks argument types against the signature (with dependent substitution), and verifies the return type is consistent with what is expected.

## Key concepts

- **Context**: A map from names to bindings. OL bindings carry an optional `fullType = (list of params, return type)`.
- **Consistency**: Structural equality where holes act as wildcards (match anything).
- **Resolution**: Substituting names for terms in an environment. Used for dependent type checking -- when `(f (x : A)) : B`, checking `(f arg)` requires substituting `arg` for `x` in `B`.
- **Modes**: The checker uses checking modes (`Program`, `Line`, `Spine`, `Argument`, `Expression`, `IdentifierMode`) to distinguish syntactic positions. Declarations appear in `Line` mode within blocks; terms being checked for types are in `Expression` mode.

## What to implement

All functions marked `failwith("TODO")` in the stub. Specifically:

1. **`resolve(env, t)`** -- Substitute identifiers in term `t` according to environment `env`. Recurse into all term variants.

2. **`resolveWithParams(wenv, t)`** -- Like `resolve` but for witness substitution. Parameterized declarations `(f x y)` with witness `w` require substituting `x`, `y` with actual arguments when `(f a b)` appears.

3. **`termConsistent(a, b)`** -- Structural consistency check. Holes match anything. Identifiers match by name. Recurse into Ap, List, Cons, Comma, Arrow, Asc.

4. **`consistent(t1, t2)`** -- Optional wrapper: `None` is consistent with everything.

5. **`lookupCtx(ctx, x)`** -- Look up an identifier in context. `Sort` is always in scope with type `Sort`. Only OL bindings are visible.

6. **`subsume(expected, inferred, from, to_)`** -- Check that inferred type is consistent with expected. Report "Too few arguments" if params remain and an expected type exists.

7. **`checkArity(expected, found, from, to_)`** -- Compare argument count, return arity error if mismatched.

8. **`ensureMode(allowed, mode, from, to_)`** -- Verify the current checking mode is in the allowed list.

9. **`extractParams(args)`** -- Extract `(name, type)` pairs from a function signature's argument list.

10. **`checkDecls(ctx, body)`** -- Fold over declaration lines, checking each in `Line` mode and threading the context.

11. **The `Postulate` case in `checkTerm`** -- Process postulate block body via `checkDecls`, then check the rest in `Program` mode.

12. **The `Identifier` case in `checkTerm`** (Expression mode) -- Look up in context, subsume against expected type.

13. **The `Asc` case in `checkTerm`** -- Handle `Line` mode (declaration), `Argument` mode (parameter binding), and fallthrough.

14. **The `Ap` case in `checkTerm`** -- Handle `Program` mode (sequence), `Spine` mode (declaration head), `Expression` mode (dependent application with arity checking).

15. **The `Hole` and `Shard`/`BuilderError` cases in `checkTerm`**.

## Testing

Run `make test` from the project root. OL checking is exercised by any test that uses postulate blocks.
