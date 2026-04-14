# Assignment 8: Blocks and Witnesses

## Overview

In this assignment you implement the **block processing and witness-and-discard mechanism** -- the core architectural innovation of Mint. You connect the OL type checker and ML type checker to handle `meta` blocks (where schemas and let-bindings are defined), and `construct` blocks (where declarations are verified by running a schema to produce witnesses, then type-checking and discarding those witnesses).

## Key concepts

- **Meta blocks** contain `schema` definitions (which bind schema closures for use by construct blocks) and `let` definitions (which bind ML expressions). Both persist across subsequent blocks.
- **Construct blocks** declare OL signatures and are annotated with a schema name. The schema is evaluated, applied to the declarations, and must produce witness terms. Each witness is type-checked against its declaration's type (with prior witnesses substituted for prior declared names). If all witnesses check, the declarations are accepted and the witnesses are discarded.
- **`metaDefsRef`**: A mutable ref tracking meta-level let definitions in definition order. The Construct case reads this to build the evaluation environment.
- **`mlBuiltins`**: The context of ML builtins (`Sort`, `fst`, `snd`, `foldl`, `true`, `false`, `Ok`, `Error`).
- **Witness substitution**: Uses `resolveWithParams` so that parameterized declarations like `(f (x : A))` with witness `w` correctly substitute arguments when `(f arg)` appears in subsequent types.

## What to implement

All block/meta/construct-related functions marked `failwith("TODO")` in the stub. The OL and ML checking functions are provided complete. Specifically:

1. **`mlBuiltins`** -- The ML builtins context. Declare `Sort` as `ML(MTerm)`, `fst`/`snd`/`foldl` as `Builtin(name)`, `true`/`false` as `ML(MBool)`, `Ok`/`Error` as `Builtin(name)`.

2. **`metaDefsRef`** -- The mutable ref for tracking meta-level let definitions.

3. **`processMeta(accInfo, accCtx, accDefs, items)`** -- Process meta block items:
   - `schema name = body` (possibly with type annotation): check body as schema type, bind as `SchemaBinding`
   - Annotated let `name : type = body`: check/infer body, bind as `MetaLet`
   - Bare let `name = body`: infer body, bind as `MetaLet`
   - Track definitions in `accDefs` for the eval environment

4. **The `Meta` case in `checkTerm`** -- Merge context with `mlBuiltins`, call `processMeta`, store definitions in `metaDefsRef`, process rest.

5. **The `Construct` case in `checkTerm`** -- The witness-and-discard pipeline:
   - Check declarations via `checkDecls`
   - Look up the schema by name
   - Build the eval environment from `metaDefsRef` (evaluate each definition, then patch closures to see the complete env)
   - Evaluate the schema body in that environment
   - Run the schema on the construct declarations via `Eval.runSchema`
   - Verify witness count matches declaration count
   - For each (declaration, witness) pair: add parameters to context, resolve expected type through witness substitution env, check witness, accumulate substitution env
   - If any witness has errors, report them on the `by` annotation
   - Process rest in the context of declared names

## Testing

Run `make test` from the project root. Block processing is exercised by any test that uses postulate/meta/construct blocks together.
