# Assignment 7: ML Checking

## Overview

In this assignment you implement the **Meta-Language (ML) type checker**. The ML is a simply-typed functional language used to write metaprograms (schemas) that produce witnesses for construct blocks. It has types `Term`, `Sort`, `Bool`, `String`, `List t`, `Result t`, `(t, t)` (pairs), and `t -> t` (functions).

The ML checker uses **bidirectional type checking**: `inferExpr` synthesizes a type from the term, while `checkExpr` pushes an expected type down into the term. Both always return `staticInfo` (never fail) -- errors are accumulated for total error localization.

## Key concepts

- **`mlType`**: The ML type grammar, defined in `MLType.re`.
- **Bidirectional checking**: `inferExpr` infers; `checkExpr` checks against an expected type. Checking mode allows lambdas, matches, and if-expressions to propagate types inward.
- **OL terms in ML**: OL terms have ML type `MTerm`. Identifiers not in scope (when no OL bindings exist) are treated as OL literals.
- **Builtins**: `fst`, `snd`, `foldl` are polymorphic builtins with custom typing rules. `Ok`/`Error` are Result constructors. `true`/`false` are Bool constants.
- **Schemas**: Always have type `List Signature -> Result (List Term)` where `Signature = (Term, List (Term, Term), Term)`.

## What to implement

All ML-related functions marked `failwith("TODO")` in the stub. The OL checking functions are provided complete. Specifically:

1. **`mlTypeToTerm(ty)`** -- Convert an `mlType` to its term representation (e.g., `MTerm` becomes `Identifier("Term")`).

2. **`termToMlType(t)`** -- Parse a term back into an `mlType`. Handle `Term`, `Sort`, `Bool`, `String`, `Signature`, `List t`, `Result t`, `Arrow`, `Comma`.

3. **`mlSubsume(expected, got, from, to_)`** -- Compare two ML types for equality, producing an error if they differ.

4. **`mlInferred(ty)`** -- Wrap an `mlType` as an `option(fullType)` for the `inferred` field.

5. **`getInferredMlType(info)`** -- Extract the ML type from a `staticInfo`'s inferred field, defaulting to `MTerm`.

6. **`inferExpr(ctx, t)`** -- Infer the ML type of an expression. Cases:
   - `Identifier`: look up in context; OL/Schema/Builtin bindings infer as `MTerm`
   - `StringLit`: infers as `MString`
   - `Hole`: produces hole info, infers as `MTerm`
   - `fst`/`snd` application: infer arg, extract pair component
   - `foldl` application: custom typing rule using init and list types
   - General `Ap`: walk arrow type, checking args; `MTerm` means OL application
   - `Fun`: infer body with pattern bound as `MTerm`, result is `MArrow(MTerm, bodyTy)`
   - `Let`: process binding (with optional type annotation), infer body in extended context
   - `Match`: infer scrutinee, check first branch to get result type, check remaining branches
   - `If`: check condition as `MBool`, infer then-branch, check else-branch
   - `Comma`: infer both sides, result is `MPair`
   - `List`: infer first element type, check rest against it
   - `Cons`: infer heads and tail, result is `MList`
   - `BinOp`: `==`/`!=` produce `MBool`; `&&`/`||` check both as `MBool`; others are `MTerm`

7. **`checkExpr(ctx, expected, t)`** -- Check an expression against an expected ML type. Cases:
   - `Hole`: produce hole info with the expected type as goal
   - `Fun`: decompose expected `MArrow`, check pattern and body
   - `Match`: infer scrutinee, check all branches against expected
   - `If`: check condition, then, else against expected
   - `Ok`/`Error` application: decompose expected `MResult`
   - `List`: if expected is `MList`, check elements; otherwise infer and subsume
   - `Let`: process binding, check body against expected
   - `foldl` application: use expected type as accumulator type
   - Fallthrough: infer and subsume

8. **`checkPat(ctx, ty, t)`** -- Check a pattern against an ML type. Handle identifiers (bind or constrain), string literals, lists, cons, commas, OL application patterns, holes.

9. **`checkOLPat(ctx, t)`** -- Check an OL pattern: identifiers in scope are constructors, not-in-scope identifiers bind as `MTerm` pattern variables.

10. **`checkSchema(ctx, body)`** -- Check a schema body against `schemaType` in the ML builtins context.

## Testing

Run `make test` from the project root.
