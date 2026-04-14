# Mint Proof Assistant — Reimplementation Assignments

Work through these assignments in order. Each one builds on the previous.
Fill in the stub functions (marked with `failwith("TODO")`) and run the
tests to verify your implementation.

## Setup

```bash
# Create a working branch
git checkout -b assignments

# For each assignment, copy its stubs into reason/src/
cp assignments/01-types-and-printing/stubs/*.re reason/src/

# Build and test
make test
```

Each assignment has:
- `stubs/` — files with function signatures and TODOs to fill in
- `README.md` — what to implement and why
- Test targets — which existing tests should pass after completion

**Note:** Stubs won't compile until you start filling in the TODOs.
The `failwith("TODO")` placeholders cause warnings about unused `rec` flags
and non-returning statements. These resolve as you implement. Copy all stubs
for a phase at once, then implement in order.

## Assignment sequence

### Phase 1: Data and Presentation
1. **Types and Printing** — ML type system + AST pretty printer

### Phase 2: Parsing Pipeline
2. **Lexer** — source text to token stream
3. **Grammar** — the Lytr grammar definition
4. **Parser** — token stream to parse tree
5. **Builder** — parse tree to AST

**Checkpoint:** after assignment 5, `make test` should pass all 146 parse tests.

### Phase 3: Type Checking
6. **OL Type Checking** — object language scope and consistency checking
7. **ML Type Checking** — meta-language bidirectional type inference
8. **Blocks and Witnesses** — meta blocks, construct blocks, eval env, witness checking

**Checkpoint:** after assignment 8, all 323 tests should pass except eval tests (64).

### Phase 4: Evaluation
9. **Evaluator Core** — expression evaluation and pattern matching
10. **Builtins and Schemas** — function application, builtins, schema execution

**Checkpoint:** after assignment 10, all 323 tests pass. All enum examples type-check.

## Files

| File | Provided | Assignment |
|------|----------|------------|
| Term.re | Yes (AST types) | — |
| Grammar.re | Yes (framework) | — |
| Error.re | Yes (error type) | — |
| Lytr_api.re | Yes (JS API glue) | — |
| MLType.re | — | 1 |
| Print.re | — | 1 |
| Lexer.re | — | 2 |
| LytrGrammar.re | — | 3 |
| Parser.re | — | 4 |
| Builder.re | — | 5 |
| Check.re | — | 6, 7, 8 |
| Eval.re | — | 9, 10 |
