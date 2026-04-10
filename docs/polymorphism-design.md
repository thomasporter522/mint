# ML Polymorphism Design Document

## Goal

Enable user-defined polymorphic recursive list functions in meta blocks:

```
meta
let reverse : List a -> List a =
  fun xs => match xs with
  | [] => []
  | [h, ...t] => (append (reverse t) [h])
  end

let map : (a -> b) -> List a -> List b =
  fun f => fun xs => match xs with
  | [] => []
  | [h, ...t] => [(f h), ...(map f t)]
  end

let append : List a -> List a -> List a =
  fun xs => fun ys => match xs with
  | [] => ys
  | [h, ...t] => [h, ...(append t ys)]
  end

let length : List a -> Term =
  fun xs => match xs with
  | [] => Z
  | [h, ...t] => (S (length t))
  end

schema enum = fun sigs =>
  let ctors = ... in
  let type_witness = foldl ... in
  ...
  end
```

## Four Changes

### 1. List cons syntax: `[h, ...t]`

**Syntax**: `[a, b, ...rest]` in both patterns and expressions. The `...` before the last element means "spread/rest."

**AST**: New node `Cons(list(term), term)` — head elements plus tail term.

**Grammar**: Add `...` as a symbol token (Uninterested/Uninterested). The builder detects `Ap(Identifier("..."), [rest])` as the last element of a bracket group and produces `Cons(heads, rest)` instead of `List(all)`.

**Evaluator**: 
- `evalExpr` for `Cons(heads, tail)`: evaluate heads and tail, concatenate into a `List`
- `matchPat` for `Cons(headPats, tailPat)`: match head elements one by one, bind tail to remainder

**Type checker**:
- `inferExpr` for `Cons`: infer heads element type, check tail is a list, return `MList(elemTy)`
- `checkPat` for `Cons`: when expected is `MList(elemTy)`, check head pats against `elemTy`, check tail pat against `MList(elemTy)`. When expected is `MTerm`, pass `MTerm` through.

**Files**: Term.re, LytrGrammar.re, Builder.re, Print.re, Eval.re, Check.re
**Size**: ~60 lines
**Risk**: Low-medium (builder spread detection is the tricky part)

### 2. Type variables

**Syntax**: Lowercase single letters `a`, `b`, `c` etc. in type annotations are type variables. Or more explicitly, any identifier not matching a known type name (`Term`, `Sort`, `Bool`, `String`, `List`, `Result`, `Signature`) is a type variable.

**MLType.re**: Add `MVar(string)` to `mlType`:
```
type mlType =
  | MTerm | MSort | MBool | MString
  | MList(mlType) | MResult(mlType)
  | MPair(mlType, mlType) | MArrow(mlType, mlType)
  | MVar(string);   (* NEW: type variable *)
```

**Subsumption with type variables**: `mlSubsume` becomes a unification-like check. When comparing `MVar("a")` against a concrete type, the variable matches anything (like `MTerm`). When two `MVar`s with the same name meet, they must unify.

The simplest approach: treat `MVar` like `MTerm` in subsumption — it matches anything. This gives us the notational convenience of type annotations without full unification. The type checker won't catch `map : (a -> b) -> List a -> List b` being applied with inconsistent `a`s, but it will catch structural errors like passing a `String` where a `List` is expected.

Full unification would be better but much more complex. For now, `MVar` = `MTerm` in checking, but the annotations serve as documentation and the checker validates the annotation structure (arrows, lists, pairs match up).

**termToMlType**: Extend to parse type annotations with variables:
```
| Identifier(s) when isLowercase(s) => Some(MVar(s))
```

**printType**: `MVar(s) => s`

**Files**: MLType.re, Check.re (termToMlType, mlSubsume, printType)
**Size**: ~30 lines
**Risk**: Low (MVar acts like MTerm, just documentation)

### 3. Type annotations on let bindings

**Syntax in meta blocks**: `let name : type = body` or bare `name : type = body`.

Already parsed! In a meta block, `name : type = body` parses as `Eq(Asc(name, type), body)`. The `processMeta` function already handles `Asc` in the name position for schema definitions (extracts name and type annotation). Extend the same handling to let definitions.

**Checking**: When a let binding has a type annotation:
1. Parse the annotation into an `mlType` via `termToMlType`
2. Check the body against that type (using `checkExpr` instead of `inferExpr`)
3. Store the annotated type (not the inferred type) in the context

This gives us:
```
let reverse : List a -> List a = fun xs => ...
```
The checker verifies the body is an arrow type returning a list. The annotated type `MArrow(MList(MVar("a")), MList(MVar("a")))` is stored and used at call sites.

**processMeta update**: The bare `Eq(name, rhs)` case already exists. Add:
```
| [{value: Eq({value: Asc({value: Identifier(n), _}, typeAnnot), _}, rhs), _}, ...rest] =>
  let annotTy = termToMlType(typeAnnot);
  let bodyInfo = switch (annotTy) {
    | Some(ty) => checkExpr(accCtx, ty, rhs)
    | None => inferExpr(accCtx, rhs)
  };
  let storedTy = switch (annotTy) { | Some(ty) => ty | None => getInferredMlType(bodyInfo) };
  let newCtx = StringMap.add(n, MetaLet(storedTy, rhs), accCtx);
  ...
```

**MetaLet change**: `MetaLet(term)` becomes `MetaLet(mlType, term)` to store the type alongside the body. The type is used when the binding is referenced in `inferExpr`.

**Files**: Check.re (processMeta, inferExpr Identifier case, MetaLet variant)
**Size**: ~40 lines
**Risk**: Low-medium (need to update all MetaLet pattern matches)

### 4. Recursive let

**The problem**: `reverse` calls itself. Currently, `let` bindings in meta are processed sequentially — a binding's body can reference PREVIOUS bindings but not itself.

**Solution**: When checking a let binding's body, add the binding itself to the context BEFORE checking. The binding's type comes from the annotation (required for recursive definitions).

```
| [{value: Eq({value: Asc({value: Identifier(n), _}, typeAnnot), _}, rhs), _}, ...rest] =>
  let annotTy = termToMlType(typeAnnot);
  switch (annotTy) {
  | Some(ty) =>
    (* Add self-reference to context for recursive checking *)
    let recCtx = StringMap.add(n, MetaLet(ty, rhs), accCtx);
    let bodyInfo = checkExpr(recCtx, ty, rhs);
    ...
  | None => (* non-annotated, non-recursive *)
    ...
  };
```

Type annotations are REQUIRED for recursive definitions. Without an annotation, the checker can't know the type before checking the body. This is standard (OCaml requires annotations for recursive types, Haskell infers but that needs HM).

**Evaluator**: The evaluator already handles recursion implicitly! When a `MetaLet` binding is looked up in the eval env, it evaluates the body. If the body references itself, it looks up the same name — which triggers another evaluation. This is lazy/call-by-name. For terminating functions like `reverse` on finite lists, this works. For non-terminating recursion, it loops (which is fine — that's a user bug, not a system bug).

Actually, there's a subtlety. The eval env is built in the Construct handler:
```
let evalEnv = StringMap.fold(
  (name, binding, acc) =>
    switch (binding) {
    | MetaLet(_, body) =>
      switch (Eval.evalExpr(acc, body)) {
      | Eval.Ok(v) => Eval.StringMap.add(name, v, acc)
      | Eval.Err(_) => acc
      }
    | _ => acc
    },
  ctx, Eval.StringMap.empty,
);
```

This evaluates each let binding eagerly when building the eval env. A recursive function like `reverse` would try to evaluate `fun xs => match xs with | [h, ...t] => (append (reverse t) [h]) | ...` — which produces a `Closure(env, pat, body)`. The `reverse` name is NOT in `env` at closure creation time because the fold hasn't finished yet.

**Fix**: Build the eval env in two passes:
1. First pass: evaluate all let bindings, creating closures. For recursive bindings, the closure captures the current (incomplete) env.
2. Second pass: patch the closures' environments to include all bindings (including self-references).

Or simpler: use a lazy/thunked approach where the eval env is a ref that gets populated incrementally. When a closure is applied, it looks up names in the CURRENT env (which by then includes all bindings).

The simplest implementation: wrap the eval env in a `ref` and populate it. Each `MetaLet` body is evaluated with access to the ref. When the resulting closure is later applied, name lookups go through the ref which now has all bindings.

```
let evalEnvRef = ref(Eval.StringMap.empty);
StringMap.iter(
  (name, binding) =>
    switch (binding) {
    | MetaLet(_, body) =>
      switch (Eval.evalExpr(evalEnvRef^, body)) {
      | Eval.Ok(v) => evalEnvRef := Eval.StringMap.add(name, v, evalEnvRef^)
      | Eval.Err(_) => ()
      }
    | _ => ()
    },
  ctx,
);
let evalEnv = evalEnvRef^;
```

But this still doesn't work because the Closure captures `evalEnvRef^` at creation time, not the final value. We need closures to look up in a shared mutable env.

**Better approach**: Change `Eval.Closure` to capture an `evalEnv ref` instead of a plain `evalEnv`:

Actually, the simplest approach: don't evaluate let bindings eagerly. Instead, store them as thunks (raw terms) in the eval env, and evaluate on demand. Change the eval env to store `mlValue | Thunk(term)`:

No — this gets complicated. The simplest correct approach for recursive closures:

1. Evaluate the body to get a `Closure(env, pat, body)`
2. The closure's `env` doesn't include self-reference yet
3. After creating the closure, add the binding `name -> closure` to the closure's own env

This is the standard "tying the knot" trick. In the Construct handler:

```
(* For each MetaLet, evaluate to get a value *)
(* Then for recursive ones, patch the closure env *)
let evalEnv = StringMap.fold(
  (name, binding, acc) =>
    switch (binding) {
    | MetaLet(_, body) =>
      switch (Eval.evalExpr(acc, body)) {
      | Eval.Ok(Eval.Closure(cEnv, pat, cbody)) =>
        (* Tie the knot: add self to closure env *)
        let selfClosure = Eval.Closure(cEnv, pat, cbody);
        let patchedEnv = Eval.StringMap.add(name, selfClosure, cEnv);
        Eval.StringMap.add(name, Eval.Closure(patchedEnv, pat, cbody), acc)
      | Eval.Ok(v) => Eval.StringMap.add(name, v, acc)
      | Eval.Err(_) => acc
      }
    | _ => acc
    },
  ctx, Eval.StringMap.empty,
);
```

This adds the closure itself to its own env. When the closure is applied and the body references `reverse`, it finds itself in the env and recurses. This works for direct recursion. Mutual recursion would need a two-pass approach.

**Files**: Check.re (processMeta, Construct eval env builder), possibly Eval.re
**Size**: ~30 lines  
**Risk**: Medium (recursive closure env patching needs care)

## Summary

| Change | Size | Risk | Dependency |
|--------|------|------|------------|
| 1. Cons syntax `[h, ...t]` | ~60 lines | Low-medium | None |
| 2. Type variables `MVar` | ~30 lines | Low | None |
| 3. Type annotations on let | ~40 lines | Low-medium | 2 (uses MVar in annotations) |
| 4. Recursive let | ~30 lines | Medium | 3 (needs annotation for recursive type) |
| **Total** | **~160 lines** | **Medium** | Sequential |

## Implementation Order

1. Cons syntax (independent, immediately useful)
2. Type variables (small, enables 3)
3. Type annotations on let (enables 4)
4. Recursive let (completes the picture)

After all four, users can write:
```
meta
let reverse : List a -> List a =
  fun xs => match xs with
  | [] => []
  | [h, ...t] => [h, ...(reverse t)]
  end
```

And use it in schemas to build generic enum witnesses.
