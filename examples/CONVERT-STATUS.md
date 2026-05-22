# Conversion procedure status

## What works

The beta-conversion procedure is installed as `coerce beta`. It now:
1. Head-reduces both terms via `#reduction`-tagged context entries (currently top-only — see "diagnosis" below).
2. Resolves metavariables via a threaded meta-map.
3. Treats OL holes (`?`) as wildcards in pattern matching and as "match-anything" sentinels in target position.
4. Compares head constructors; recurses into children pairwise.
5. Combines sub-proofs via hard-coded congruence rules for core formers.

All 496 JS tests pass (1 pre-existing `church.mint` grammar failure is unrelated).

## Diagnosis: deep-recursion isn't infinite, but extremely redundant

You were right to be skeptical of "5 minutes." I added a file-trace inside the `print` builtin (Melange `fs.appendFileSync` to `/tmp/mint-trace.log`, bypassing vitest's stdout capture) and re-ran the deep alg on lap-eq's elaboration.

After 110 seconds:
- **31,843 head-reduce calls**
- **27 unique terms**
- Linear growth (~290 calls/sec); not exponential
- `U` head-reduced 7,499 times; `X` 5,777; `sap X U A x` 2,368; etc.
- 57 distinct `coerce` invocations from the elaborator over the same elaboration

So it's not an infinite loop. The elaborator calls `coerce` 57 times to bridge lap-eq's type, and each call walks the same subtrees from scratch. Each head-reduce visits each subtree position; with the deep algorithm, the inner recursion re-traverses already-normalised children to verify they're stuck.

The "5 minutes" hang is just `57 × 60 hr-calls × overhead`. Roughly linear in (#coerce-invocations × tree-size).

The fundamental issue is the elaborator re-asking the same conversion question many times. With nothing shared across coerce calls, the procedure has no way to cache progress.

## What's now in place (your morning items)

### A1 — kernel: trace log

`reason/src/Eval.re` `print` builtin also appends to `/tmp/mint-trace.log` via Melange `fs.appendFileSync`. Used here for the diagnosis above; can be left in place — it's silent if `fs` isn't bound.

### D — distinguish metalang `?` from OL holes

Kernel: added `Meta(int)` constructor to `cML`. `embedOL` now sends `OLMeta(n)` to `Meta(n)` (instead of degrading to `Hole(User)`). `==` propagates Hole as unknown: `Hole == anything` returns `Hole`. (`Hole == Hole` also returns `Hole` — strict propagation.)

User-level builtins:
- `is-hole t : Bool` — true iff `t` is an OL hole.
- `is-meta t : Bool` — true iff `t` is an OL meta.
- `meta-id t : String` — meta's integer id, stringified.

Migration: every `(t == ?)` check in the `examples/*.mint` procedures was replaced with `(is-hole t)`. The `?` in metalang now means strict "unknown".

### B — hole-aware matching

`fun-convert.mint`'s `match-term` now special-cases target = OL hole:
- Match succeeds.
- Every binder occurring in the pat-subtree is bound to `?` via `bind-each-to-hole` (unless already bound by a non-hole occurrence).
- Conflict resolution: if a binder is already bound to a hole, a later non-hole occurrence overwrites via `bind-or-update`.
- Result: a rule like `sap (sap (lk X A) a) x → a` fires against `sap ? x`, substitutes the hole-bound `a`, and rewrites to `?` — exactly the example you gave.

### C — meta-instantiation in convert (user-level)

`convert` now threads a `mmap : List (Term, Term)` of meta-solutions:
- Signature: `convert : ctx -> mmap -> Term -> Term -> Result (Term, mmap)`.
- `resolve-meta mmap t` substitutes solved metas before any comparison.
- When one side is a meta and the other isn't, bind: `(Ok ((refl other), mmap ++ [(meta, other)]))`.
- When both sides are different metas, skip binding (cycle-avoidance) and treat as refl on either.
- Recursive `convert-norm` and `convert-list` accept and return the map.

The map is local to one coerce invocation — solutions don't propagate back to the elaborator's meta context (that would need kernel-level mutable state, which you flagged as risky). Within a single call, this still helps when a meta appears in multiple positions.

## What's still failing on lap-eq

Same 3 diagnostics:

```
[mark]: Inconsistency
  (expected sap (sto ? U) U (to ?) ?,
   got sap X U (lsap X (lsto X A (sap U (sto X U) (lk X U) U)) U (lto X A) B) x)
[warning]: Implicit arguments not fully solved (×2)
```

`head-reduce` is currently top-only in `fun-convert.mint` because the deep variants are too expensive to validate. The deep "all children" variant (your spec) does eventually finish but well past 5 minutes; the "single-step first reducible child" variant has the same issue. Both because of the 57× coerce-invocation factor, not because of looping.

Possible next steps:
- **Cross-coerce caching:** expose a mutable map at the procedure level (your kernel-level option) so solutions persist between coerce calls. This is the biggest lever.
- **Smarter elaborator:** if the elaborator could deduplicate coerce calls or batch them, the 57× factor would shrink. That's a kernel change.
- **Test the algorithm on lap-eq:** with the mutable-map option, validate whether the deep variant + meta-map + hole-aware matching actually completes the lap-eq case.

Happy to do the mutable-map work next if you want.

## Meta-language additions still in tree

Helpers in `fun-convert.mint`:
- `top-loop`, `head-reduce-args`, `all-refl`, `single-step`, `step-first-arg`, `top-loop-args`, `refls-for`, `list-set` (deep-recursion helpers, currently bypassed).
- `collect-binders`, `bind-or-update`, `update-binding`, `bind-each-to-hole` (hole-aware matching).
- `resolve-meta` (meta substitution).

Kernel additions:
- `print` now writes to `/tmp/mint-trace.log` in addition to stdout.
- `Meta(int)` constructor on ML.
- `is-hole`, `is-meta`, `meta-id` builtins.
- Equality propagates Hole as unknown.
