-- Test 2: cong rules. Single sto-cong with a sub-reduction.
-- Setup: a type former `wrap` with no congruence, but a reduction.

postulate
U : U
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
cast (A B : U) (e : eq A B) (a : A) : B
sym (A B : U) (a : A) (b : B) (e1 : eq a b) : eq b a
trans (A B C : U) (a : A) (b : B) (c : C) (e1 : eq a b) (e2 : eq b c) : eq a c
meta
    newtag #reduction
postulate
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq

postulate
sto (A B : U) : U
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
redex (P : U) : U
redex-eq (P : U) : eq (redex P) P
#reduction redex-eq

postulate
TestP : U
TestQ : U
test-witness : sto TestP TestQ

meta
    has-reduction : ((List Tag) -> Bool) = fun tags =>
        (foldl (fun acc => fun t => acc || (t == #reduction)) false tags)
    lookup : (Term -> ((List (Term, Term)) -> (Result Term))) = fun k => fun xs =>
        (foldl (fun acc => fun pair =>
            match acc with
            | Ok _ => acc
            | Error _ =>
                match pair with
                | (key, val) => if (key == k) then (Ok val) else acc end
                end
            end) (Error "not found") xs)
    param-names : ((List (Term, Term)) -> (List Term)) = fun params =>
        (foldl (fun acc => fun p => match p with | (n, _) => (append acc [n]) end) [] params)
    fill-args : ((List Term) -> ((List (Term, Term)) -> (List Term))) = fun binders => fun bindings =>
        (foldl (fun acc => fun b =>
            match (lookup b bindings) with
            | Ok v => (append acc [v])
            | Error _ => (append acc [?])
            end) [] binders)
    reverse-terms : ((List Term) -> (List Term)) = fun xs =>
        (foldl (fun acc => fun x => x :: acc) [] xs)
    member : (Term -> ((List Term) -> Bool)) = fun x => fun xs =>
        (foldl (fun acc => fun e => acc || (e == x)) false xs)

    match-term : ((List Term) -> ((List (Term, Term)) -> (Term -> (Term -> (Result (List (Term, Term))))))) =
        fun binders => fun bindings => fun pat => fun term =>
            if (is-hole pat) then (Ok bindings) else
            let pp = (decompose pat) in
            let (ph, pa) = pp in
            match pa with
            | [] =>
                if (member ph binders) then
                    match (lookup ph bindings) with
                    | Ok existing => if (existing == term) then (Ok bindings) else (Error "binder conflict") end
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

    align-match : ((List Term) -> ((List (Term, Term)) -> ((List Term) -> ((List Term) -> (Result (List (Term, Term))))))) =
        fun binders => fun bindings => fun rps => fun rts =>
            match rps with
            | [] => (Ok bindings)
            | p :: ps =>
                match rts with
                | [] => (Error "pattern wider than term")
                | t :: ts =>
                    match (match-term binders bindings p t) with
                    | Ok b1 => (align-match binders b1 ps ts)
                    | Error msg => (Error msg)
                    end
                end
            end

    subst-list : ((List (Term, Term)) -> ((List Term) -> (List Term))) = fun bindings => fun ts =>
        (foldl (fun acc => fun t => (append acc [(subst bindings t)])) [] ts)
    subst : ((List (Term, Term)) -> (Term -> Term)) = fun bindings => fun t =>
        let p = (decompose t) in
        let (h, args) = p in
        match args with
        | [] => match (lookup h bindings) with | Ok v => v | Error _ => t end
        | _ :: _ => (apply (subst bindings h) (subst-list bindings args))
        end

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

    try-top : ((List Signature) -> (Term -> (Result (Term, Term)))) = fun ctx => fun term =>
        (foldl (fun acc => fun entry =>
            match acc with
            | Ok _ => acc
            | Error _ =>
                match entry with
                | (_, _, _, tags) => if (has-reduction tags) then (try-rule entry term) else acc end
                end
            end) (Error "no rule fired") ctx)

    head-reduce : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun t =>
        match (try-top ctx t) with
        | Ok (t-next, step-proof) =>
            let (t-final, rest-proof) = (head-reduce ctx t-next) in
            (t-final, (trans step-proof rest-proof))
        | Error _ => (t, (refl t))
        end

    apply-cong : (Term -> ((List Term) -> (Result Term))) = fun head => fun proofs =>
        if (head == sto) then
            match proofs with
            | [eA, eB] => (Ok (sto-cong eA eB))
            | _ => (Error "sto-cong: wrong arity")
            end
        else (Error "no cong rule for this head")
        end

    convert-list : ((List Signature) -> ((List Term) -> ((List Term) -> (Result (List Term))))) =
        fun ctx => fun xs => fun ys =>
            match (xs, ys) with
            | ([], []) => (Ok [])
            | (x :: xt, y :: yt) =>
                match (convert ctx x y) with
                | Ok p =>
                    match (convert-list ctx xt yt) with
                    | Ok ps => (Ok (p :: ps))
                    | Error msg => (Error msg)
                    end
                | Error msg => (Error msg)
                end
            | _ => (Error "argument-count mismatch")
            end

    convert : ((List Signature) -> (Term -> (Term -> (Result Term)))) =
        fun ctx => fun t1 => fun t2 =>
            if (is-hole t1) then (Ok (refl t2)) else
            if (is-hole t2) then (Ok (refl t1)) else
            let (t1r, p1) = (head-reduce ctx t1) in
            let (t2r, p2) = (head-reduce ctx t2) in
            if (t1r == t2r) then
                (Ok (trans p1 (sym p2)))
            else
                let d1 = (decompose t1r) in
                let d2 = (decompose t2r) in
                let (h1, a1) = d1 in
                let (h2, a2) = d2 in
                if (is-hole h1) then (Ok (trans p1 (trans (refl t2r) (sym p2)))) else
                if (is-hole h2) then (Ok (trans p1 (trans (refl t1r) (sym p2)))) else
                if (h1 == h2) then
                    match (convert-list ctx a1 a2) with
                    | Ok proofs =>
                        match (apply-cong h1 proofs) with
                        | Ok mid => (Ok (trans p1 (trans mid (sym p2))))
                        | Error msg => (Error msg)
                        end
                    | Error msg => (Error msg)
                    end
                else (Error "head constructors disagree")
                end end end
            end end end

    coerce beta = fun ctx => fun expected => fun found => fun contents =>
        match (convert ctx found expected) with
        | Ok proof => (Ok (cast proof contents))
        | Error msg => (Error msg)
        end

    -- Schema that returns test-witness for any decl.
    schema id-s = fun ctx => fun args => (Ok [test-witness])

-- Decl 1: expected sto TestP TestQ, witness sto TestP TestQ. No coerce.
construct by id-s
t1 : sto TestP TestQ

-- Decl 2: expected sto (redex TestP) TestQ. Reduces to sto TestP TestQ.
-- Coerce should produce a cast via sto-cong with sub-conversions.
construct by id-s
t2 : sto (redex TestP) TestQ

-- Decl 3: expected sto (redex TestP) (redex TestQ). Both args reduce.
construct by id-s
t3 : sto (redex TestP) (redex TestQ)
