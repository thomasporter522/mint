-- Conversion procedure for the fun.mint language.
-- Builds a proof of equality between two terms by:
--   1) head-reducing both terms (applying #reduction-tagged rewrites
--      at the root until none fire),
--   2) checking the resulting head constructors agree,
--   3) recursing on the children and combining sub-proofs via the
--      hard-coded congruence rule for that head.
-- Installed as the `beta` coerce so type mismatches in value positions
-- get auto-bridged with a `cast` carrying the equality proof.

postulate
sort : sort
U : U
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
cast (A B : U) (e : eq A B) (a : A) : B
sym (A B : U) (a : A) (b : B) (e1 : eq a b) : eq b a
trans (A B C : U) (a : A) (b : B) (c : C) (e1 : eq a b) (e2 : eq b c) : eq a c
meta
    newtag #reduction
postulate
sto (A B : U) : U
sap (A B : U) (f : sto A B) (a : A) : B
to (A : U) : sto (sto A U) U
ap (A : U) (B : sto A U) (f : sap (to A) B) (a : A) : sap B a
postulate
-- cast-eq lets the conversion reduce `cast e a` to `a` when a proof
-- exists, so it stays out of head-reduction's eye.
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
sap-cong (A1 A2 B1 B2 : U) (f1 : sto A1 B1) (f2 : sto A2 B2) (a1 : A1) (a2 : A2) (e1 : eq f1 f2) (e2 : eq a1 a2) : eq (sap f1 a1) (sap f2 a2)
-- Congruence rules for core formers. These mirror sto-cong / sap-cong
-- but for to, ap, eq. The B-params of ap-cong must have type
-- `sto Ai U` (not bare `U`), because ap's B-param is a type-family
-- indexed by A.
to-cong (A1 A2 : U) (e1 : eq A1 A2) : eq (to A1) (to A2)
ap-cong (A1 A2 : U) (B1 : sto A1 U) (B2 : sto A2 U)
        (f1 : sap (to A1) B1) (f2 : sap (to A2) B2)
        (a1 : A1) (a2 : A2)
        (e1 : eq f1 f2) (e2 : eq a1 a2)
        : eq (ap f1 a1) (ap f2 a2)
eq-cong (A1 A2 B1 B2 : U) (a1 : A1) (a2 : A2) (b1 : B1) (b2 : B2) (eA : eq A1 A2) (eB : eq B1 B2) (ea : eq a1 a2) (eb : eq b1 b2) : eq (eq a1 b1) (eq a2 b2)

meta
    -- True iff this binding's tag list carries #reduction.
    has-reduction : ((List Tag) -> Bool) = fun tags =>
        (foldl (fun acc => fun t => acc || (t == #reduction)) false tags)

    -- Assoc-list lookup, by `==`.
    lookup : (Term -> ((List (Term, Term)) -> (Result Term))) = fun k => fun xs =>
        (foldl (fun acc => fun pair =>
            match acc with
            | Ok _ => acc
            | Error _ =>
                match pair with
                | (key, val) => if (key == k) then (Ok val) else acc end
                end
            end) (Error "not found") xs)

    -- Names from a list of (name, type) param tuples.
    param-names : ((List (Term, Term)) -> (List Term)) = fun params =>
        (foldl (fun acc => fun p =>
            match p with
            | (n, _) => (append acc [n])
            end) [] params)

    -- For each binder, retrieve its bound value (or ? if unbound).
    fill-args : ((List Term) -> ((List (Term, Term)) -> (List Term))) = fun binders => fun bindings =>
        (foldl (fun acc => fun b =>
            match (lookup b bindings) with
            | Ok v => (append acc [v])
            | Error _ => (append acc [?])
            end) [] binders)

    -- Reverse a list of terms (used by align-match for end-alignment).
    reverse-terms : ((List Term) -> (List Term)) = fun xs =>
        (foldl (fun acc => fun x => x :: acc) [] xs)

    -- List membership by ==.
    member : (Term -> ((List Term) -> Bool)) = fun x => fun xs =>
        (foldl (fun acc => fun e => acc || (e == x)) false xs)

    -- Try to match `pat` against `term`. Identifiers in `binders` are
    -- treated as pattern variables; everything else must match literally
    -- (or recurse). For Ap, we right-align so the pattern may elide
    -- leading implicit type arguments that the target carries.
    match-term : ((List Term) -> ((List (Term, Term)) -> (Term -> (Term -> (Result (List (Term, Term))))))) =
        fun binders => fun bindings => fun pat => fun term =>
            -- Hole in pattern (`?`) acts as a wildcard. This shows up
            -- when a rule's LHS has impl-inserted metas -- after
            -- embedding the metas surface as holes, and they should
            -- match whatever the target has in that slot.
            if (pat == ?) then (Ok bindings) else
            let pp = (decompose pat) in
            let (ph, pa) = pp in
            match pa with
            | [] =>
                if (member ph binders) then
                    match (lookup ph bindings) with
                    | Ok existing =>
                        if (existing == term) then (Ok bindings) else (Error "binder conflict") end
                    | Error _ => (Ok (append bindings [(ph, term)]))
                    end
                else
                    if (pat == term) then (Ok bindings) else (Error "atom mismatch") end
                end
            | _ :: _ =>
                let tp = (decompose term) in
                let (th, ta) = tp in
                match ta with
                | [] => (Error "expected ap, got atom")
                | _ :: _ =>
                    match (match-term binders bindings ph th) with
                    | Ok b1 => (align-match binders b1 (reverse-terms pa) (reverse-terms ta))
                    | Error msg => (Error msg)
                    end
                end
            end end

    -- Walk the (reversed) pattern/target arg lists in parallel; surplus
    -- target args on the LEFT are skipped (those are the leading
    -- implicits the pattern elides).
    align-match : ((List Term) -> ((List (Term, Term)) -> ((List Term) -> ((List Term) -> (Result (List (Term, Term))))))) =
        fun binders => fun bindings => fun rps => fun rts =>
            match rps with
            | [] => (Ok bindings)
            | p :: ps =>
                match rts with
                | [] =>
                    -- Pattern still has leading args but target is exhausted.
                    -- This happens when the pattern was elaborated with impl
                    -- args at its start while the target is in as-written
                    -- form (no impls). Succeed iff the leftover pattern args
                    -- are all wildcards.
                    if (p == ?) then (align-match binders bindings ps []) else (Error "pattern wider than term") end
                | t :: ts =>
                    match (match-term binders bindings p t) with
                    | Ok b1 => (align-match binders b1 ps ts)
                    | Error msg => (Error msg)
                    end
                end
            end

    -- Substitute pattern bindings into a term.
    subst-list : ((List (Term, Term)) -> ((List Term) -> (List Term))) = fun bindings => fun ts =>
        (foldl (fun acc => fun t => (append acc [(subst bindings t)])) [] ts)
    subst : ((List (Term, Term)) -> (Term -> Term)) = fun bindings => fun t =>
        let p = (decompose t) in
        let (h, args) = p in
        match args with
        | [] =>
            match (lookup h bindings) with
            | Ok v => v
            | Error _ => t
            end
        | _ :: _ => (apply (subst bindings h) (subst-list bindings args))
        end

    -- Try one #reduction-tagged context entry as a rewrite rule.
    -- Recognises retTypes shaped `eq _ _ LHS RHS`; matches the target
    -- against LHS, then returns (rhs-substituted, rule-applied-as-proof).
    -- The proof has the same param order as the rule itself.
    try-rule : ((Term, (List (Term, Term)), Term, (List Tag)) -> (Term -> (Result (Term, Term)))) =
        fun sig => fun term =>
            match sig with
            | (name, params, retType, _) =>
                let binders = (param-names params) in
                let rp = (decompose retType) in
                let (rh, ra) = rp in
                if (rh == eq) then
                    match ra with
                    | [_, _, lhs, rhs] =>
                        match (match-term binders [] lhs term) with
                        | Ok bindings =>
                            let reduced = (subst bindings rhs) in
                            let proof = (apply name (fill-args binders bindings)) in
                            (Ok (reduced, proof))
                        | Error msg => (Error msg)
                        end
                    | _ => (Error "retType is not 4-arg eq")
                    end
                else (Error "retType head is not eq") end
            end

    -- Iterate context's #reduction-tagged entries; return the first
    -- (reduced-term, proof) that fires. Generic -- no rule names baked
    -- in.
    -- Iterate context's #reduction-tagged entries; return the first
    -- (reduced-term, proof) that fires. We pre-filter by checking that
    -- the rule's LHS head matches the target's head -- this skips most
    -- irrelevant rules without invoking match-term.
    try-top : ((List Signature) -> (Term -> (Result (Term, Term)))) = fun ctx => fun term =>
        let term-head = (fst (decompose term)) in
        (foldl (fun acc => fun entry =>
            match acc with
            | Ok _ => acc
            | Error _ =>
                match entry with
                | (_, _, retType, tags) =>
                    if (has-reduction tags) then
                        match (decompose retType) with
                        | (rh, [_, _, lhs, _]) =>
                            if (rh == eq) then
                                let lhs-head = (fst (decompose lhs)) in
                                if (lhs-head == term-head) then (try-rule entry term) else acc end
                            else acc end
                        | _ => acc
                        end
                    else acc end
                end
            end) (Error "no rule fired") ctx)

    -- Map a function returning (Term, Term) over a list, accumulating
    -- two parallel lists.
    refls-for : ((List Term) -> (List Term)) = fun ts =>
        (foldl (fun acc => fun t => (append acc [(refl t)])) [] ts)

    -- Replace the i-th element of a list with v.
    list-set : ((List Term) -> ((List Term) -> ((List Term) -> (List Term)))) =
        fun prefix => fun suffix => fun v-list =>
            -- prefix (reversed) ++ v-list ++ suffix
            (append (foldl (fun acc => fun x => x :: acc) v-list prefix) suffix)

    -- Try a one-step reduction inside a list of args: walk left-to-right,
    -- and for the first arg whose single-step succeeds, return the new
    -- list-of-args plus a proofs-list (refls for non-changed positions
    -- and the actual proof for the changed one). Returns Error if no
    -- arg can be single-stepped.
    --
    -- The proofs-list is what apply-cong consumes.
    step-first-arg : ((List Signature) -> ((List Term) -> ((List Term) -> (Result ((List Term), (List Term)))))) =
        fun ctx => fun prefix-rev => fun args =>
            match args with
            | [] => (Error "no arg can step")
            | a :: rest =>
                match (single-step ctx a) with
                | Ok (a-new, a-proof) =>
                    let prefix = (foldl (fun acc => fun x => x :: acc) [] prefix-rev) in
                    let new-args = (append (append prefix [a-new]) rest) in
                    let proofs = (append (append (refls-for prefix) [a-proof]) (refls-for rest)) in
                    (Ok (new-args, proofs))
                | Error _ => (step-first-arg ctx (a :: prefix-rev) rest)
                end
            end

    -- Single step: one rewrite, either at the top or in the first
    -- child that admits one. Returns Ok (t-new, proof : eq t t-new) or Error.
    single-step : ((List Signature) -> (Term -> (Result (Term, Term)))) =
        fun ctx => fun t =>
            match (try-top ctx t) with
            | Ok x => (Ok x)
            | Error _ =>
                let d = (decompose t) in
                let (h, args) = d in
                match args with
                | [] => (Error "atom: no children to step")
                | _ :: _ =>
                    match (step-first-arg ctx [] args) with
                    | Ok (new-args, proofs) =>
                        match (apply-cong h proofs) with
                        | Ok cong-proof => (Ok ((apply h new-args), cong-proof))
                        | Error msg => (Error msg)
                        end
                    | Error msg => (Error msg)
                    end
                end
            end

    -- Top-loop: exhaust top-level reductions on `t`.
    top-loop : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun t =>
        match (try-top ctx t) with
        | Ok (t-next, step-proof) =>
            let (t-final, rest-proof) = (top-loop ctx t-next) in
            (t-final, (trans step-proof rest-proof))
        | Error _ => (t, (refl t))
        end

    -- Map top-loop over an argument list (no deep recursion).
    top-loop-args : ((List Signature) -> ((List Term) -> ((List Term), (List Term)))) =
        fun ctx => fun args =>
            (foldl (fun acc => fun a =>
                match acc with
                | (reduced-acc, proofs-acc) =>
                    let (a-r, a-p) = (top-loop ctx a) in
                    ((append reduced-acc [a-r]), (append proofs-acc [a-p]))
                end) ([], []) args)

    -- Map head-reduce over an argument list.
    head-reduce-args : ((List Signature) -> ((List Term) -> ((List Term), (List Term)))) =
        fun ctx => fun args =>
            (foldl (fun acc => fun a =>
                match acc with
                | (reduced-acc, proofs-acc) =>
                    let (a-r, a-p) = (head-reduce ctx a) in
                    ((append reduced-acc [a-r]), (append proofs-acc [a-p]))
                end) ([], []) args)

    -- Check whether all proofs in a list are refls.
    all-refl : ((List Term) -> Bool) = fun proofs =>
        (foldl (fun acc => fun p =>
            acc && (match (decompose p) with
                    | (h, _) => (h == refl)
                    end)
        ) true proofs)

    -- Head-reduce: top-loop, then deeply normalize each child, then
    -- re-try top. KEY OPTIMIZATION: after rebuilding with normalized
    -- children, we only `top-loop` (not full head-reduce) because the
    -- children are already in NF. If top-loop fires, the result has
    -- a new shape; THEN we recurse fully.
    head-reduce : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun t =>
        let (t1, p1) = (top-loop ctx t) in
        let d = (decompose t1) in
        let (h, args) = d in
        match args with
        | [] => (t1, p1)
        | _ :: _ =>
            let (args-reduced, args-proofs) = (head-reduce-args ctx args) in
            if (all-refl args-proofs) then (t1, p1) else
            match (apply-cong h args-proofs) with
            | Ok cong-proof =>
                let t2 = (apply h args-reduced) in
                -- Children are NF: only top-loop on t2 (no deep recurse).
                let (t2-top, top-p) = (top-loop ctx t2) in
                if (t2-top == t2) then
                    -- top didn't fire; t2 is fully normalized.
                    (t2, (trans p1 cong-proof))
                else
                    -- top fired; t2-top has fresh shape that may need
                    -- another deep pass.
                    let (t-final, rest-p) = (head-reduce ctx t2-top) in
                    (t-final, (trans p1 (trans cong-proof (trans top-p rest-p))))
                end
            | Error _ => (t1, p1)
            end end
        end

    -- Build an eq-proof between two argument lists by zipping convert
    -- over them. Order of cong applications follows the order in which
    -- the congruence postulate takes its proof args (which is the same
    -- as the order of the term's children).
    -- Compare two arg lists pairwise, right-aligned. When lengths
    -- differ, the longer list's LEADING extras are treated as impls
    -- (bridged by refl against the corresponding wildcard on the
    -- shorter side). This handles the gap between elaborated terms
    -- (which carry impls) and meta-language-substituted terms (which
    -- usually don't).
    --
    -- We reverse both, consume pairs from the front, and when one
    -- runs out the OTHER's remaining items get paired with `?` so
    -- convert's wildcard branch generates refls. The output proof
    -- list is in original (un-reversed) order.
    convert-list : ((List Signature) -> ((List Term) -> ((List Term) -> (Result (List Term))))) =
        fun ctx => fun xs => fun ys =>
            (convert-list-rev ctx (reverse-terms xs) (reverse-terms ys) [])

    -- Helper: walks reversed xs, ys; accumulates proofs in `acc` in
    -- the correct (un-reversed) order. Args are already normalized
    -- (head-reduce-args normalized them in the parent's head-reduce),
    -- so we use convert-norm -- saves re-reducing already-normal terms.
    convert-list-rev : ((List Signature) -> ((List Term) -> ((List Term) -> ((List Term) -> (Result (List Term)))))) =
        fun ctx => fun rxs => fun rys => fun acc =>
            match (rxs, rys) with
            | ([], []) => (Ok acc)
            | (x :: xt, y :: yt) =>
                match (convert-norm ctx x y) with
                | Ok p => (convert-list-rev ctx xt yt (p :: acc))
                | Error msg => (Error msg)
                end
            | ([], y :: yt) =>
                match (convert-norm ctx ? y) with
                | Ok p => (convert-list-rev ctx [] yt (p :: acc))
                | Error msg => (Error msg)
                end
            | (x :: xt, []) =>
                match (convert-norm ctx x ?) with
                | Ok p => (convert-list-rev ctx xt [] (p :: acc))
                | Error msg => (Error msg)
                end
            end

    -- Build a cong proof from a head and the per-arg eq-proofs. Each
    -- core former gets a hard-coded dispatch matching its `<head>-cong`
    -- postulate's signature.
    --
    -- The proofs list runs in the same order as the term's args. The
    -- postulates differ in how many leading TYPE args precede each
    -- proof; we trust the elaborator's implicit-arg insertion to fill
    -- those.
    apply-cong : (Term -> ((List Term) -> (Result Term))) = fun head => fun proofs =>
        if (head == sto) then
            match proofs with
            | [eA, eB] => (Ok (sto-cong eA eB))
            | _ => (Error "sto-cong: wrong arity")
            end
        else if (head == sap) then
            match proofs with
            -- sap (A B : U) (f : sto A B) (a : A) : 4 args; cong's first
            -- two e-proofs cover the type args (eA, eB), but
            -- sap-cong's user-facing proofs are e1 (over f) and e2
            -- (over a). The TYPE-arg eqs are produced via convert too.
            | [eA, eB, ef, ea] => (Ok (sap-cong ef ea))
            | _ => (Error "sap-cong: wrong arity")
            end
        else if (head == to) then
            match proofs with
            | [eA] => (Ok (to-cong eA))
            | _ => (Error "to-cong: wrong arity")
            end
        else if (head == ap) then
            match proofs with
            | [eA, eB, ef, ea] => (Ok (ap-cong ef ea))
            | _ => (Error "ap-cong: wrong arity")
            end
        else if (head == eq) then
            match proofs with
            | [eA, eB, ea, eb] => (Ok (eq-cong eA eB ea eb))
            | _ => (Error "eq-cong: wrong arity")
            end
        else
            -- No congruence rule for this head: we can only succeed if
            -- the args are all already-refl. We check by inspecting the
            -- proofs -- if any is non-trivial, fail.
            (Error "no congruence rule for this head")
        end end end end end

    -- Compare two ALREADY-normalized terms. Skips the head-reduce step
    -- because head-reduce on the parent already normalized children.
    -- This is what convert-list/convert-norm recursively call.
    convert-norm : ((List Signature) -> (Term -> (Term -> (Result Term)))) =
        fun ctx => fun t1r => fun t2r =>
            if (t1r == ?) then (Ok (refl t2r)) else
            if (t2r == ?) then (Ok (refl t1r)) else
            if (t1r == t2r) then (Ok (refl t1r)) else
            let d1 = (decompose t1r) in
            let d2 = (decompose t2r) in
            let (h1, a1) = d1 in
            let (h2, a2) = d2 in
            if (h1 == ?) then (Ok (refl t2r)) else
            if (h2 == ?) then (Ok (refl t1r)) else
            if (h1 == h2) then
                match (convert-list ctx a1 a2) with
                | Ok proofs =>
                    match (apply-cong h1 proofs) with
                    | Ok mid => (Ok mid)
                    | Error msg => (Error msg)
                    end
                | Error msg => (Error msg)
                end
            else (Error "head constructors disagree")
            end end end end end end

    -- Top-level convert: head-reduce both, then compare as normalized.
    convert : ((List Signature) -> (Term -> (Term -> (Result Term)))) =
        fun ctx => fun t1 => fun t2 =>
            if (t1 == ?) then (Ok (refl t2)) else
            if (t2 == ?) then (Ok (refl t1)) else
            if (t1 == t2) then (Ok (refl t1)) else
            let (t1r, p1) = (head-reduce ctx t1) in
            let (t2r, p2) = (head-reduce ctx t2) in
            match (convert-norm ctx t1r t2r) with
            | Ok mid => (Ok (trans p1 (trans mid (sym p2))))
            | Error msg => (Error msg)
            end
            end end end

    -- Install as a coerce procedure. When the elaborator detects a
    -- type mismatch in a value position, convert is called on the
    -- expected and found types; on success the user's value is wrapped
    -- in `cast proof value`.
    coerce beta = fun ctx => fun expected => fun found => fun contents =>
        match (convert ctx found expected) with
        | Ok proof => (Ok (cast proof contents))
        | Error msg => (Error msg)
        end

postulate
lk (X A : U) : sto A (sto X A)
lk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (lk X A) a) x) a
#reduction lk-eq
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq
lsap (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) : sto X B
lsap-eq (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) (x : X) :
    eq (sap (lsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction lsap-eq
lto (X : U) (A : sto X U) : sap (to X) (lsto (lsto A (sap lk U)) (sap lk U))
lto-eq (X : U) (A : sto X U) (x : X) : eq (ap (lto X A) x) (to (sap A x))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) : sap (to X) (lsap B a)
-- Test: original lap-eq had a hand-rolled cast. Strip it and let the
-- conversion coerce produce the bridging proof. Tag lines above are
-- applied to the context as they are processed, so lap-eq's coerce
-- sees them when it runs.
lap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) (x : X) :
    eq (ap (lap f a) x)
        (ap (ap f x) (ap a x))
