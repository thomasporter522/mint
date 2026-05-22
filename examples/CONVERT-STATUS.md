# Conversion procedure status

## What works

The beta-conversion procedure is implemented and installed as a `coerce beta`. It:
1. Head-reduces both terms via `#reduction`-tagged context entries.
2. Compares head constructors; recurses into children pairwise.
3. Combines sub-proofs via hard-coded congruence rules for core formers (`sap-cong`, `sto-cong`, `to-cong`, `ap-cong`, `eq-cong`).
4. Treats `?` (holes / unsolved metas) as wildcards in both pattern matching and recursion.

All 496 tests pass.

## Followups from the morning review

### 1. Inline tag application — DONE

Fixed: tag lines now feed into the context the moment they're encountered, interleaved with decls by source position. `Check.re`'s `checkBlock` (Postulate/Construct cases) now builds a combined `decl/tag-line` stream sorted by start offset and folds over it, so a `#reduction` tag above `lap-eq` is visible inside `lap-eq`'s elaboration without splitting the postulate block. Verified by reverting the lap/lap-eq block split; tests still green.

### 2. Head-filter optimisation — already user-defined

The `try-top` head-filter (skip every reduction rule whose LHS head doesn't match the target's head) lives **inside the user's procedure** (in `fun-convert.mint` and each test file), not the kernel. It's just an `if lhs-head == term-head then try-rule ... else acc` check on top of the foldl over context. Nothing in the kernel changed for it — it's a procedure-level early-exit. So this stays out of the meta-language.

### 3. Improved head-reduce algorithm — implemented, too slow to verify

Implemented your "rewrite at top until stuck, then reduce all children, then re-loop" algorithm. Tested in three variants:

- **Deep child recursion** (head-reduce each child fully): completes on every simple test but doesn't finish on `fun-convert.mint`'s `lap-eq` within 5 minutes.
- **Single-step / first-reducible-child** (one rewrite per outer iteration, drilling down to find any reducible position): same — doesn't finish on lap-eq in 5 minutes.
- **One-level-deep** (children get `top-loop` only, no recursion into grandchildren): finishes lap-eq in ~1.6 seconds with no change to the lap-eq errors.

In all three variants the procedure code is in `fun-convert.mint` (kept around `single-step`, `step-first-arg`, `top-loop`, `head-reduce-args`, `all-refl`, `top-loop-args`) but `head-reduce` is currently aliased to `top-loop`-only so the test surfaces lap-eq's diagnostics.

The full-depth variants don't infinite-loop — each iteration makes monotonic progress — they're just very expensive on lap-eq's tree shape. Each outer `head-reduce` call re-walks the subtree, and the elaborator invokes coerce many times during lap-eq's impl-arg resolution (each invocation pays the full cost). I tried short-circuiting redundant work via:
- `convert-norm` so internal recursion doesn't re-head-reduce already-normal children.
- `t1 == t2` early exit before any reduction.

These speed up the top-only case from 14s → 1s but don't unstick the deep variants.

**Suspected root cause:** with deep recursion, every `apply-cong h proofs` emits a cong-postulate application whose impl args the elaborator solves by calling coerce again. Many cong applications across many coerce invocations seems to expand into a tree of nested coerce calls. (Speculative — I didn't add instrumentation to confirm.)

### 4. Current `lap-eq` diagnostics

```
21183-21191 [mark]: Inconsistency
  (expected sap (sto ? U) U (to ?) ?,
   got sap X U (lsap X (lsto X A (sap U (sto X U) (lk X U) U)) U (lto X A) B) x)
21151-21153 [warning]: Implicit arguments not fully solved
21180-21182 [warning]: Implicit arguments not fully solved
```

Per your morning message: this is the implicit-solving-order issue you wanted to discuss in detail if the algorithm change didn't unblock it. I can't yet confirm the algorithm would change the outcome, because the deep variants don't terminate on this input. Happy to spell out lap-eq's elaboration trace as you suggested.

## Meta-language additions still in tree

- `print` builtin: `print x` / `print "label" x`. Returns its arg, logs to console. Polymorphic.
- `top-loop`, `top-loop-args`, `head-reduce-args`, `all-refl`, `single-step`, `step-first-arg`, `refls-for`, `list-set` are defined in `fun-convert.mint`. `head-reduce` is wired to `top-loop` only.

## Kernel changes

- `Check.re`: `checkBlock` interleaves decls and tag lines by source order. `processTagLines` → `processTagLine` (single line at a time). `interleaveBlock`/`processBlockItems` helpers added.
