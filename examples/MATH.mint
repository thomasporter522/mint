postulate
sort : sort
-- universe levels
level : sort
lz : level
ls (l : level) : level
lmax (l1 l2 : level) : level
Ul (l : level) : Ul (ls l)
level-leq (l1 l2 : level) : sort
level-leq-refl (l : level) : level-leq l l
level-leq-trans (l1 l2 l3 : level) (leq1 : level-leq l1 l2) (leq2 : level-leq l2 l3) : level-leq l1 l3
level-leq-lz (l : level) : level-leq lz l
level-leq-ls (l : level) : level-leq l (ls l)
level-leq-ls-cong (l1 l2 : level) (leq : level-leq l1 l2) : level-leq (ls l1) (ls l2)
level-leq-lmax-1 (l1 l2 : level) : level-leq l1 (lmax l1 l2)
level-leq-lmax-2 (l1 l2 : level) : level-leq l2 (lmax l1 l2)
level-leq-lmax-eq-1 (l1 l2 : level) (leq : level-leq l1 l2) : level-leq (lmax l1 l2) l2 
level-leq-lmax-eq-2 (l1 l2 : level) (leq : level-leq l2 l1) : level-leq (lmax l1 l2) l1
-- level-eq (l1 l2 : level) : sort
-- level-eq-leq (l1 l2 : level) (leq1 : level-leq l1 l2) (leq2 : level-leq l2 l1) : level-eq l1 l2
level-coerce (l1 : level) (l2 : level) (eq : level-leq l1 l2) (e : Ul l1) : Ul l2
-- function types
to (l1 l2 : level) (A : Ul l1) (B : Ul l2) : Ul (lmax l1 l2)
ap (l1 l2 : level) (A : Ul l1) (B : Ul l2) (f : to A B) (a : A) : B
pi (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) : Ul (lmax l1 l2)
dap (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) (f : pi A B) (a : A) : ap B a
-- equations
eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) : Ul (lmax l1 l2)
refl (l : level) (A : Ul l) (a : A) : eq a a
cast (l : level) (A B : Ul l) : to (eq A B) (to A B)
-- todo: use a unified eq eliminator
sym (l : level) (A B : Ul l) (a : A) (b : B) : to (eq a b) (eq b a)
trans (l : level) (A B C : Ul l) (a : A) (b : B) (c : C) : to (eq a b) (to (eq b c) (eq a c))

cong-ap (l1 l2 : level)
  (A : Ul l1) (B : Ul l2)
  (f : to A B) (g : to A B)
  (a : A) (b : A) 
  : to (eq f g) 
    (to (eq a b) 
      (eq (ap f a) (ap g b)))
cong-to (l1 l2 : level)
  (A1 A2 : Ul l1) (B1 B2 : Ul l2)
  (eA : eq A1 A2) (eB : eq B1 B2)
  : eq (to A1 B1) (to A2 B2)
combinator-constant (l1 l2 : level) 
  (A : Ul l1) (B : Ul l2) 
  : to A (to B A)
combinator-constant-eq (l1 l2 : level) 
  (A : Ul l1) (B : Ul l2) 
  (x : A) (y : B) 
  : eq (ap (ap (combinator-constant ) x) y) x
combinator-ap (l1 l2 l3 : level) 
  (A : Ul l1) (B : Ul l2) (C : Ul l3) 
  : to (to A (to B C)) (to (to A B) (to A C))
combinator-ap-eq (l1 l2 l3 : level) 
  (A : Ul l1) (B : Ul l2) (C : Ul l3) 
  (f : to A (to B C)) 
  (g : to A B) 
  (x : A) 
  : eq (ap (ap (ap combinator-ap f) g) x) (ap (ap f x) (ap g x))
combinator-to (l1 l2 l3 : level) 
  (A : Ul l1)
  : to (to A (Ul l2)) (to (to A (Ul l3)) (to A (Ul (lmax l2 l3))))
combinator-to-eq (l1 l2 l3 : level) 
  (A : Ul l1)
  (t1 : to A (Ul l2))
  (t2 : to A (Ul l3)) 
  (x : A) 
  : eq (ap (ap (ap (combinator-to ) t1) t2) x) (to (ap t1 x) (ap t2 x))
meta
  schema definition =
    fun outer => fun s => match s with
    | [(a, [], _),
       (a_eq, [], eq _ _ _ _ a body)]
        => (Ok [body, (refl)])
    | _ => (Error "invalid definition")
    end
construct by definition
U1 : Ul (ls (ls lz))
U1-eq : eq U1 (Ul (ls lz))
construct by definition
U : U1
U-eq : eq U (ap (ap cast (ap sym U1-eq)) (Ul lz))
meta
    abs = fun x => fun e => fun l1 => fun l2 => fun A => fun B =>
  if e == x
  then 
    let witness = (ap (ap (combinator-ap) (combinator-constant)) (combinator-constant l1 l1 A A)) in
    let proof = (ap (ap trans (combinator-ap-eq)) (combinator-constant-eq)) in
    (witness, proof)
  else match e with
  | (ap lp1 lp2 Aprime Bprime f a) =>
      let f-res = (abs x f l1 (lmax lp1 l2) A (to lp1 l2 Aprime B)) in
      let a-res = (abs x a l1 lp1 A Aprime) in
      let fw = (fst f-res) in
      let fp = (snd f-res) in
      let aw = (fst a-res) in
      let ap2 = (snd a-res) in
      let witness = (ap (ap (combinator-ap) fw) aw) in
      let proof = (ap (ap trans (combinator-ap-eq)) (ap (ap cong-ap fp) ap2)) in
      (witness, proof)
  | (to lp1 lp2 e1 e2) =>
      -- [x](to e1 e2) at type Ul (lmax lp1 lp2): combinator-to A (λx.e1) (λx.e2),
      -- proof via combinator-to-eq + cong-to over the two recursive proofs.
      let e1-res = (abs x e1 l1 (ls lp1) A (Ul lp1)) in
      let e2-res = (abs x e2 l1 (ls lp2) A (Ul lp2)) in
      let t1 = (fst e1-res) in
      let t1-proof = (snd e1-res) in
      let t2 = (fst e2-res) in
      let t2-proof = (snd e2-res) in
      let witness = (ap (ap (combinator-to) t1) t2) in
      let proof = (ap (ap trans (combinator-to-eq)) (cong-to t1-proof t2-proof)) in
      (witness, proof)
  | _ =>
      ((ap (combinator-constant) e), (combinator-constant-eq))
  end
  end
    schema abstraction = fun outer => fun s => match s with
  | [(f, f-params, (to l1 l2 A B)),
     (_, eq-params, (eq _ _ _ _ (ap _ _ _ _ f-applied x-id) body))] =>
      -- f's param names, in declaration order. Two folds: the first
      -- collects (fst p) values (giving reverse order), the second
      -- reverses again.
      let f-param-names-rev = (foldl (fun acc => fun p => (fst p) :: acc) [] f-params) in
      let f-param-names = (foldl (fun acc => fun n => n :: acc) [] f-param-names-rev) in
      -- Reconstruct what the equation's inner-ap function slot should
      -- hold: f applied to its own parameters. For unparameterised f
      -- this is just the identifier f; for f with N params it is
      -- Ap(f, [p_1, …, p_N]).
      let expected-f-applied =
        match f-params with
        | [] => f
        | _ => (apply f f-param-names)
        end in
      -- And the equation's parameter list should be exactly f's
      -- parameters followed by the abstraction variable (x-id : A).
      let f-params-rev : (List (Term, Term)) =
        (foldl (fun acc => fun p => p :: acc) [] f-params) in
      let expected-eq-params : (List (Term, Term)) =
        (foldl (fun acc => fun p => p :: acc) [(x-id, A)] f-params-rev) in
      if (f-applied == expected-f-applied) && (eq-params == expected-eq-params)
      then
        let result = (abs x-id body l1 l2 A B) in
        (Ok [(fst result), (snd result)])
      else (Error "abstraction: equation's params must be f's params followed by (x : A), and its LHS must be (ap (f p_1 … p_N) x)")
      end
  | _ => (Error "abstraction: expected (f : to l1 l2 A B) and (f-beta (p_1 …) (x : A) : eq (ap (f p_1 …) x) body)")
  end
postulate
void : Ul lz
void-case (Ml : level) (M : Ul Ml) : to void M
unit : Ul lz
trivial : unit
unit-case (Ml : level) (M : Ul Ml) (star-case : M) : to unit M
unit-comp (Ml : level) (M : Ul Ml) (star-case : M) : eq (ap (unit-case star-case) trivial) star-case
sum (lA lB : level) (A : Ul lA) (B : Ul lB) : Ul (lmax lA lB)
inl (lA lB : level) (A : Ul lA) (B : Ul lB) (a : A) : sum A B
inr (lA lB : level) (A : Ul lA) (B : Ul lB) (b : B) : sum A B
sum-case (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) : to (sum A B) M
sum-case-inl (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) (a : A) : eq (ap (sum-case f g) (inl a)) (ap f a)
sum-case-inr (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) (b : B) : eq (ap (sum-case f g) (inr b)) (ap g b)
N : Ul lz
zero : N
suc : to N N
plus : to N (to N N)
construct by abstraction
double : to N N
double-beta (n : N) : eq (ap double n) (ap (ap plus n) n)
meta
    reverse : ((List Term) -> (List Term)) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs)
    reverse-triples : ((List (Term, (Term, Term))) -> (List (Term, (Term, Term)))) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs)
    append : ((List Term) -> ((List Term) -> (List Term))) = fun xs => fun ys => (foldl (fun acc => fun x => x :: acc) ys (reverse xs))
    concat : ((List (List Term)) -> (List Term)) = fun xss => (foldl (fun acc => fun xs => (append acc xs)) [] xss)
    build-injs-and-type : ((List Term) -> ((List Term), (Term, Term))) = fun rest =>
    (foldl (fun acc => fun _ =>
        let prev-injs = (fst acc) in
        let prev-pair = (snd acc) in
        let prev-type = (fst prev-pair) in
        let prev-level = (snd prev-pair) in
        let cur-type = (sum lz prev-level unit prev-type) in
        let cur-level = (lmax lz prev-level) in
        let wrapped = (reverse (foldl (fun a => fun inj =>
        (inr lz prev-level unit prev-type inj) :: a) [] prev-injs)) in
        ((inl lz prev-level unit prev-type trivial) :: wrapped, (cur-type, cur-level))
    ) ([trivial], (unit, lz)) rest)
    build-elim : (Term -> (Term -> ((List Term) -> ((List Term) -> Term)))) = fun lM => fun mvar => fun case-vars => fun rest =>
    let rev-cvs = (reverse case-vars) in
    match rev-cvs with
    | last-cv :: remaining-cvs =>
        let last-f = (ap lM (lmax lz lM) mvar (to lz lM unit mvar)
                        (combinator-constant lM lz mvar unit)
                        last-cv) in
        (fst (foldl (fun acc => fun cv =>
        let prev-arr = (fst acc) in
        let prev-pair = (snd acc) in
        let prev-type = (fst prev-pair) in
        let prev-level = (snd prev-pair) in
        let cur-type = (sum lz prev-level unit prev-type) in
        let cur-level = (lmax lz prev-level) in
        let f = (ap lM (lmax lz lM) mvar (to lz lM unit mvar)
                    (combinator-constant lM lz mvar unit)
                    cv) in
        let new-arr = (sum-case lz prev-level lM unit prev-type mvar f prev-arr) in
        (new-arr, (cur-type, cur-level))
        ) (last-f, (unit, lz)) remaining-cvs))
    | _ => trivial
    end
    build-proofs : (Term -> (Term -> ((List Term) -> ((List Term) -> (List Term))))) = fun lM => fun mvar => fun case-vars => fun rest =>
    let rev-cvs = (reverse case-vars) in
    match rev-cvs with
    | last-cv :: remaining-cvs =>
        let last-f = (ap lM (lmax lz lM) mvar (to lz lM unit mvar)
                        (combinator-constant lM lz mvar unit)
                        last-cv) in
        let last-proof = (combinator-constant-eq lM lz mvar unit last-cv trivial) in
        let result = (foldl (fun acc => fun cv =>
        let prev-triples-and-elim = (fst acc) in
        let prev-triples = (fst prev-triples-and-elim) in
        let prev-elim = (snd prev-triples-and-elim) in
        let prev-pair = (snd acc) in
        let prev-type = (fst prev-pair) in
        let prev-level = (snd prev-pair) in
        let cur-type = (sum lz prev-level unit prev-type) in
        let cur-level = (lmax lz prev-level) in
        let f = (ap lM (lmax lz lM) mvar (to lz lM unit mvar)
                    (combinator-constant lM lz mvar unit)
                    cv) in
        let cur-elim = (sum-case lz prev-level lM unit prev-type mvar f prev-elim) in
        let inl-proof = (ap (ap (trans lM mvar mvar mvar
            (ap cur-level lM cur-type mvar cur-elim (inl lz prev-level unit prev-type trivial))
            (ap lz lM unit mvar f trivial)
            cv)
            (sum-case-inl lz prev-level lM unit prev-type mvar f prev-elim trivial))
            (combinator-constant-eq lM lz mvar unit cv trivial)) in
        let inl-triple = (inl-proof, ((inl lz prev-level unit prev-type trivial), cv)) in
        let wrapped = (reverse-triples (foldl (fun a => fun triple =>
            let old-proof = (fst triple) in
            let old-inj = (fst (snd triple)) in
            let old-tc = (snd (snd triple)) in
            let new-proof = (ap (ap (trans lM mvar mvar mvar
            (ap cur-level lM cur-type mvar cur-elim (inr lz prev-level unit prev-type old-inj))
            (ap prev-level lM prev-type mvar prev-elim old-inj)
            old-tc)
            (sum-case-inr lz prev-level lM unit prev-type mvar f prev-elim old-inj))
            old-proof) in
            (new-proof, ((inr lz prev-level unit prev-type old-inj), old-tc)) :: a
        ) [] prev-triples)) in
        ((inl-triple :: wrapped, cur-elim), (cur-type, cur-level))
        ) (([(last-proof, (trivial, last-cv))], last-f), (unit, lz)) remaining-cvs) in
        (reverse (foldl (fun acc => fun triple =>
        (fst triple) :: acc) [] (fst (fst result))))
    | _ => []
    end

    schema enum = fun outer => fun s => match s with
    | [(type-name, [], (Ul lT)),
        (case-name, [(_, level), (mvar, (Ul lM))], (to _ _ type-name mvar))]
        => (Ok [void, (void-case lM mvar)])
    | [(type-name, [], (Ul lT)),
        (ctor, [], type-name),
        (case-name, [(_, level), (mvar, (Ul lM)), (tc, mvar)], (to _ _ type-name mvar)),
        (eq-name, [(_, level), (mvar2, (Ul lM2)), (tc2, mvar2)], _)]
        => (Ok [unit, trivial, (unit-case lM mvar tc), (unit-comp lM2 mvar2 tc2)])
    | (type-name, [], (Ul lT)) :: all-rest =>
        let found-params = (foldl (fun acc => fun entry =>
        if (fst acc) == true then acc
        else match entry with
            | (_, [], _) => acc
            | (_, params, _) => (true, params)
            end
        end
        ) (false, [(trivial, trivial)]) all-rest) in
        match (snd found-params) with
        | (_, level) :: (mvar, (Ul lM)) :: tcs =>
        let rev-case-vars = (foldl (fun acc => fun p =>
            (fst p) :: acc) [] tcs) in
        let case-vars = (reverse rev-case-vars) in
        match case-vars with
        | _ :: rest-case-vars =>
            let iat = (build-injs-and-type rest-case-vars) in
            let injs = (fst iat) in
            let coprod-pair = (snd iat) in
            let coprod-type = (fst coprod-pair) in
            let coprod-level = (snd coprod-pair) in
            let elim-arr = (build-elim lM mvar case-vars rest-case-vars) in
            let proofs = (build-proofs lM mvar case-vars rest-case-vars) in
            (Ok (concat [[coprod-type], injs, [elim-arr], proofs]))
        | _ => (Error "false ctors") end
        | _ => (Error "bad params") end
    | _ => (Error "unrecognized") end
construct by enum
falsity : Ul lz
falsity-case (lM : level) (M : Ul lM) : to falsity M
construct by enum
myunit : Ul lz
mytrivial : myunit
myunit-case (lM : level) (M : Ul lM) (mytrivial-case : M) : to myunit M
myunit-case-trivial (lM : level) (M : Ul lM) (mytrivial-case : M) : eq (ap (myunit-case mytrivial-case) mytrivial) mytrivial-case
construct by enum
bool : Ul (lmax lz lz)
true : bool
false : bool
bool-case (lM : level) (M : Ul lM) (true-case false-case : M) : to bool M
bool-case-true (lM : level) (M : Ul lM) (true-case false-case : M) : eq (ap (bool-case true-case false-case) true) true-case
bool-case-false (lM : level) (M : Ul lM) (true-case false-case : M) : eq (ap (bool-case true-case false-case) false) false-case
-- construct by enum
-- triple : Ul (lmax lz (lmax lz lz))
-- a : triple
-- b : triple
-- c : triple
-- triple-case (lM : level) (M : Ul lM) (a-case b-case c-case : M) : to triple M
-- triple-case-a (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (ap (triple-case a-case b-case c-case) a) a-case
-- triple-case-b (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (ap (triple-case a-case b-case c-case) b) b-case
-- triple-case-c (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (ap (triple-case a-case b-case c-case) c) c-case
meta
    schema cases = fun outer => fun block => match block with
    | (name, [], (to _ lM T M)) :: eq-decls =>
        -- find the case-eliminator E for T in outer (works for any arity)
        let e-info = (foldl (fun acc => fun entry =>
            if (fst acc) == true then acc
            else match entry with
                | (E, (_, level) :: (m, (Ul _)) :: _, (to _ _ T-cand m)) =>
                    if T-cand == T then (true, E) else acc end
                | _ => acc
                end
            end
        ) (false, trivial) outer) in
        if (fst e-info) == false then (Error "cases: no eliminator for T")
        else
            let E = (snd e-info) in
            -- pull case values from each equation in block order; we trust
            -- the user lists equations in slot order
            let cv-vals = (reverse (foldl (fun acc => fun decl =>
                match decl with
                | (_, [], (eq _ _ _ _ (ap _ _ _ _ name-cand _) v)) =>
                    if name-cand == name then v :: acc else acc end
                | _ => acc
                end
            ) [] eq-decls)) in
            let args = (lM :: (M :: cv-vals)) in
            let fn-witness = (apply E args) in
            let comp-witnesses = (reverse (foldl (fun acc => fun decl =>
                match decl with
                | (_, [], (eq _ _ _ _ (ap _ _ _ _ name-cand ctor) _)) =>
                    if name-cand == name then
                        let comp-info = (foldl (fun a => fun entry =>
                            if (fst a) == true then a
                            else match entry with
                                | (cn, params, (eq _ _ _ _ (ap _ _ _ _ inner-fn c-cand) _)) =>
                                    -- the right comp rule applies E to its own
                                    -- params (lM, M, then each case-var), so the
                                    -- inner-fn must equal (apply E param-names)
                                    let param-names = (reverse (foldl (fun a2 => fun p =>
                                        (fst p) :: a2) [] params)) in
                                    let expected-fn = (apply E param-names) in
                                    if inner-fn == expected-fn && c-cand == ctor
                                    then (true, cn) else a end
                                | _ => a
                                end
                            end
                        ) (false, trivial) outer) in
                        if (fst comp-info) == true
                        then (apply (snd comp-info) args) :: acc
                        else acc
                        end
                    else acc
                    end
                | _ => acc
                end
            ) [] eq-decls)) in
            (Ok (fn-witness :: comp-witnesses))
        end
    | _ => (Error "cases: expected (f : to T M) followed by equations") end
construct by cases
when-pigs-fly : to void (eq zero (ap suc zero)) 
construct by cases
not : to bool bool 
not-true : eq (ap not true) false
not-false : eq (ap not false) true
construct by cases
is-true : to bool (Ul lz) 
is-true-true : eq (ap is-true true) unit
is-true-false : eq (ap is-true false) void
-- construct by cases
-- rotate : to triple triple 
-- rotate-a : eq (ap rotate a) b
-- rotate-b : eq (ap rotate b) c
-- rotate-c : eq (ap rotate c) a
construct by abstraction
lnot (l : level) : to (Ul l) (Ul (lmax l lz))
lnot-eq (l : level) (p : Ul l) : eq (ap lnot p) (to p void)
construct by abstraction
true-neq-false-abs : to (eq true false) void
true-neq-false-abs-eq (p : eq true false) : eq void void (ap true-neq-false-abs p) 
  (ap (ap cast (ap (ap trans (ap sym is-true-true)) (ap (ap trans (ap (ap cong-ap refl) p)) is-true-false))) trivial)
construct by definition
true-neq-false : ap (lnot) (eq true false)
true-neq-false-eq : eq true-neq-false (ap (ap cast (ap sym lnot-eq)) true-neq-false-abs)
postulate
-- W A B: well-founded trees with node shapes A and child-arity B : A -> Type.
-- sup a f: a node of shape a with children f : (B a) -> W A B.
w (lA lB : level) (A : Ul lA) (B : to A (Ul lB)) : Ul (lmax lA lB)
sup (lA lB : level) (A : Ul lA) (B : to A (Ul lB))
  (a : A) (f : to (ap B a) (w A B)) : w A B
-- non-dependent eliminator. The step's codomain
--   (a : A) |- (B a -> W A B) -> (B a -> M) -> M
-- is built with combinator-to / combinator-constant so it is a closed
-- `to A (Ul _)` family.
w-case (lA lB lM : level) (A : Ul lA) (B : to A (Ul lB)) (M : Ul lM)
  (step : pi A
    (ap (ap (combinator-to)
            (ap (ap (combinator-to) B) (ap (combinator-constant) (w A B))))
        (ap (ap (combinator-to)
                (ap (ap (combinator-to) B) (ap (combinator-constant) M)))
            (ap (combinator-constant) M))))
  : to (w A B) M
-- w-app step a: step "applied at a" in pre-unfolded function form. The
-- kernel does not reduce `ap` on combinators, so (dap step a) is only
-- propositionally a 2-arg function; w-app is the coerced form taken
-- as a primitive.
w-app (lA lB lM : level) (A : Ul lA) (B : to A (Ul lB)) (M : Ul lM)
  (step : pi A
    (ap (ap (combinator-to)
            (ap (ap (combinator-to) B) (ap (combinator-constant) (w A B))))
        (ap (ap (combinator-to)
                (ap (ap (combinator-to) B) (ap (combinator-constant) M)))
            (ap (combinator-constant) M))))
  (a : A)
  : to (to (ap B a) (w A B)) (to (to (ap B a) M) M)
w-case-sup (lA lB lM : level) (A : Ul lA) (B : to A (Ul lB)) (M : Ul lM)
  (step : pi A
    (ap (ap (combinator-to)
            (ap (ap (combinator-to) B) (ap (combinator-constant) (w A B))))
        (ap (ap (combinator-to)
                (ap (ap (combinator-to) B) (ap (combinator-constant) M)))
            (ap (combinator-constant) M))))
  (a : A) (f : to (ap B a) (w A B))
  : eq (ap (w-case step) (sup a f))
       (ap (ap (w-app step a) f)
           (ap (ap (combinator-ap) (ap (combinator-constant) (w-case step))) f))
meta
-- todo: induction


construct by induction
N : Ul lz 
zero : N 
suc : to N N 
N-rec : ?

-- construct by quotient
-- Z : Ul lz
-- class : to ()