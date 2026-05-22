# Conversion procedure — overnight progress

## What works

The beta-conversion procedure is implemented and installed as a `coerce beta`. It:
1. Head-reduces both terms via `#reduction`-tagged context entries.
2. Compares head constructors; recurses into children pairwise.
3. Combines sub-proofs via hard-coded congruence rules for core formers (`sap-cong`, `sto-cong`, `to-cong`, `ap-cong`, `eq-cong`).
4. Treats `?` (holes / unsolved metas) as wildcards in both pattern matching and recursion.

Test files passing cleanly:
- `examples/test-convert-simple.mint` — single-step reduction `redex P → P`.
- `examples/test-convert-cong.mint` — reduction inside `sto`-cong (`sto (redex P) Q → sto P Q`).
- `examples/test-convert-deep.mint` — 3-step reduction chain `w1 → w2 → w3 → base`, nested.
- `examples/test-convert-chain.mint` — 4-step chains.
- `examples/test-convert-eq.mint` — eq-typed witnesses.
- `examples/test-convert-sap.mint` — sap-typed scenarios.
- `examples/test-convert-mixed.mint` — multiple combinations.
- `examples/test-convert-fail.mint` — correctly reports failure when types are unrelated.

All 496 tests in the JS suite pass.

## What's still failing

`examples/fun-convert.mint` is the original target: it strips the manual casts from `lap-eq`'s body and asks the conversion to produce them. The procedure runs but returns Error — the test still shows 3 errors in `lap-eq`'s `(ap f x)` position. Diagnostics:

- The coerce IS being invoked (verified via temporary `print` debug traces).
- All needed `#reduction` rules are visible in the coerce's context (had to split lap/lap-eq into their own postulate block so the previous block's tag lines are applied before lap-eq is elaborated).
- `head-reduce` of the outer sap pattern-matches against `lsap-eq`'s LHS and would substitute correctly… but the recursive convert on the inner args runs into shape mismatches (`lsap (...)` standalone vs `to ?` standalone, with no reduction rule connecting them at that level).

The procedure's structural limit: when a sub-position has the wrong head and no top-level reduction reaches inside it, the recursion gets stuck. lap-eq's case relies on the outer `sap (lsap …) x` form reducing, then re-recursing — which it does — but the impl-arg metas of the outer `ap` haven't been solved by the time the coerce sees the expected type, so the comparison hits unresolved holes in awkward positions.

## Meta-language additions

- **`print`** builtin: `print x` logs `x` and returns it. `print "label" x` prefixes a label. Used during overnight tracing; left in place since it's useful for debugging conversion-style procedures. Polymorphic (returns same type as its arg).
- **`try-top`** in the conversion procedure now pre-filters reduction rules by head — drops every rule whose LHS head doesn't match the current term's head before invoking `match-term`. Major speedup once the context contains many reductions.

## Kernel changes

None of substance. The conversion procedure is fully in user space.
