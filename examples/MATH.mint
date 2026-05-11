postulate
sort : sort
-- -- universe levels
level : sort
lz : level
ls (l : level) : level
lmax (l1 l2 : level) : level
Ul (l : level) : Ul (ls l)
level-eq (l1 l2 : level) : sort
lmax-refl (l : level) : level-eq l l
lmax-sym (l1 l2 : level) (eq : level-eq l1 l2) : level-eq l2 l1
lmax-idem (l : level) : level-eq (lmax l l) l
-- level-coerce (l1 : level) (l2 : level) (eq : level-eq l1 l2) (e : Ul l1) : Ul l2
-- equations
eq (l : level) (A B : Ul l) (a : A) (b : B) : Ul l
refl (l : level) (A : Ul l) (a : A) : eq a a
sym (l : level) (A B : Ul l) (a : A) (b : B) (e : eq a b) : eq b a
trans (l : level) (A B C : Ul l) (a : A) (b : B) (c : C) (e1 : eq a b) (e2 : eq b c) : eq a c
cast (l : level) (A B : Ul l) (e : eq A B) (a : A) : B
Ul-cong (l1 l2 : level) (my-eq : level-eq l1 l2) : (eq ? (Ul (ls l1)) (Ul (ls l2)) (Ul l1) (Ul l2))
-- function types
to (l1 l2 : level) (A : Ul l1) (B : Ul l2) : Ul (lmax l1 l2)
ap (l1 l2 : level) (A : Ul l1) (B : Ul l2) (f : to A B) (a : A) : B

pi (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) : Ul (lmax l1 l2)
dap (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) (f : pi A B) (a : A) : ap B a

cong-ap (l1 l2 : level) 
  (A : Ul l1) (B : Ul l2) 
  (f : to A B) (g : to A B) 
  (a : A) (b : A) 
  (ef : eq f g) (ea : eq a b) 
  : eq (ap f a) (ap g b)
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
  : eq (ap (ap (ap (combinator-ap ) f) g) x) (ap (ap f x) (ap g x))
meta
  schema definition =
    fun s => match s with
    | [(a, [], _),
       (a_eq, [], eq _ _ _ a body)]
        => (Ok [body, (refl body)])
    | _ => (Error "invalid definition")
    end
construct by definition
U1 : Ul (ls (ls lz))
U1-eq : eq U1 (Ul (ls lz))
construct by definition
U : U1
U-eq : eq U (cast (sym U1-eq) (Ul lz))
meta
    abs = fun x => fun e => fun l1 => fun l2 => fun A => fun B =>
  if e == x
  then (
      -- I = S K K, witness for [x]x at type A (level l1)
      (ap (lmax l1 (lmax l1 l1)) (lmax l1 l1)
        (to l1 (lmax l1 l1) A (to l1 l1 A A))
        (to l1 l1 A A)
        (ap (lmax l1 (lmax (lmax l1 l1) l1)) (lmax (lmax l1 (lmax l1 l1)) (lmax l1 l1))
          (to l1 (lmax (lmax l1 l1) l1) A (to (lmax l1 l1) l1 (to l1 l1 A A) A))
          (to (lmax l1 (lmax l1 l1)) (lmax l1 l1) (to l1 (lmax l1 l1) A (to l1 l1 A A)) (to l1 l1 A A))
          (combinator-ap l1 (lmax l1 l1) l1 A (to l1 l1 A A) A)
          (combinator-constant l1 (lmax l1 l1) A (to l1 l1 A A)))
        (combinator-constant l1 l1 A A))
    ,
      (trans l1 A A A
        (ap l1 l1 A A
          (ap (lmax l1 (lmax l1 l1)) (lmax l1 l1)
            (to l1 (lmax l1 l1) A (to l1 l1 A A))
            (to l1 l1 A A)
            (ap (lmax l1 (lmax (lmax l1 l1) l1)) (lmax (lmax l1 (lmax l1 l1)) (lmax l1 l1))
              (to l1 (lmax (lmax l1 l1) l1) A (to (lmax l1 l1) l1 (to l1 l1 A A) A))
              (to (lmax l1 (lmax l1 l1)) (lmax l1 l1) (to l1 (lmax l1 l1) A (to l1 l1 A A)) (to l1 l1 A A))
              (combinator-ap l1 (lmax l1 l1) l1 A (to l1 l1 A A) A)
              (combinator-constant l1 (lmax l1 l1) A (to l1 l1 A A)))
            (combinator-constant l1 l1 A A))
          x)
        (ap (lmax l1 l1) l1 (to l1 l1 A A) A
          (ap l1 (lmax (lmax l1 l1) l1) A (to (lmax l1 l1) l1 (to l1 l1 A A) A)
            (combinator-constant l1 (lmax l1 l1) A (to l1 l1 A A))
            x)
          (ap l1 (lmax l1 l1) A (to l1 l1 A A)
            (combinator-constant l1 l1 A A)
            x))
        x
        (combinator-ap-eq l1 (lmax l1 l1) l1 A (to l1 l1 A A) A
          (combinator-constant l1 (lmax l1 l1) A (to l1 l1 A A))
          (combinator-constant l1 l1 A A)
          x)
        (combinator-constant-eq l1 (lmax l1 l1) A (to l1 l1 A A)
          x
          (ap l1 (lmax l1 l1) A (to l1 l1 A A)
            (combinator-constant l1 l1 A A)
            x)))
    )
  else match e with
  | (ap lp1 lp2 Aprime Bprime f a) =>
      let f-res = (abs x f l1 (lmax lp1 l2) A (to lp1 l2 Aprime B)) in
      let a-res = (abs x a l1 lp1 A Aprime) in
      let fw = (fst f-res) in
      let fp = (snd f-res) in
      let aw = (fst a-res) in
      let ap2 = (snd a-res) in
      let witness =
        (ap (lmax l1 lp1) (lmax l1 l2)
          (to l1 lp1 A Aprime)
          (to l1 l2 A B)
          (ap (lmax l1 (lmax lp1 l2)) (lmax (lmax l1 lp1) (lmax l1 l2))
            (to l1 (lmax lp1 l2) A (to lp1 l2 Aprime B))
            (to (lmax l1 lp1) (lmax l1 l2) (to l1 lp1 A Aprime) (to l1 l2 A B))
            (combinator-ap l1 lp1 l2 A Aprime B)
            fw)
          aw) in
      let proof =
        (trans l2 B B B
          (ap l1 l2 A B witness x)
          (ap lp1 l2 Aprime B
            (ap l1 (lmax lp1 l2) A (to lp1 l2 Aprime B) fw x)
            (ap l1 lp1 A Aprime aw x))
          (ap lp1 l2 Aprime B f a)
          (combinator-ap-eq l1 lp1 l2 A Aprime B fw aw x)
          (cong-ap lp1 l2 Aprime B
            (ap l1 (lmax lp1 l2) A (to lp1 l2 Aprime B) fw x)
            f
            (ap l1 lp1 A Aprime aw x)
            a
            fp
            ap2)) in
      (witness, proof)
  | _ =>
      ((ap l2 (lmax l1 l2) B (to l1 l2 A B)
          (combinator-constant l2 l1 B A)
          e),
       (combinator-constant-eq l2 l1 B A e x))
  end
  end
    schema abstraction = fun s => match s with
  | [(f, [], (to l1 l2 A B)), (_, [(x, _)], (eq _ _ _ (ap _ _ _ _ f x) body))] =>
      let result = (abs x body l1 l2 A B) in
      (Ok [(fst result), (snd result)])
  | _ => (Error "abstraction: expected (f : to l1 l2 A B) and (f-beta (x : A) : eq l2 B B (ap l1 l2 A B f x) body)")
  end
postulate
void : Ul lz
void-case (Ml : level) (M : Ul Ml) (v : void) : M
unit : Ul lz
star : unit
unit-rec (Ml : level) (M : Ul Ml) (star-case : M) (u : unit) : M
unit-comp (Ml : level) (M : Ul Ml) (star-case : M) : eq (unit-rec star-case star) star-case
sum (lA lB : level) (A : Ul lA) (B : Ul lB) : Ul (lmax lA lB)
inl (lA lB : level) (A : Ul lA) (B : Ul lB) (a : A) : sum A B
inr (lA lB : level) (A : Ul lA) (B : Ul lB) (b : B) : sum A B
sum-case (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) : to (sum A B) M
sum-case-inl (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) (a : A) : eq (ap (sum-case f g) (inl a)) (ap f a)
sum-case-inr (lA lB lM : level) (A : Ul lA) (B : Ul lB) (M : Ul lM) (f : to A M) (g : to B M) (b : B) : eq (ap (sum-case f g) (inr b)) (ap g b)
N : Ul lz
zero : N
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
        ((inl lz prev-level unit prev-type star) :: wrapped, (cur-type, cur-level))
    ) ([star], (unit, lz)) rest)
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
    | _ => star
    end
    build-proofs : (Term -> (Term -> ((List Term) -> ((List Term) -> (List Term))))) = fun lM => fun mvar => fun case-vars => fun rest =>
    let rev-cvs = (reverse case-vars) in
    match rev-cvs with
    | last-cv :: remaining-cvs =>
        let last-f = (ap lM (lmax lz lM) mvar (to lz lM unit mvar)
                        (combinator-constant lM lz mvar unit)
                        last-cv) in
        let last-proof = (combinator-constant-eq lM lz mvar unit last-cv star) in
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
        let inl-proof = (trans lM mvar mvar mvar
            (ap cur-level lM cur-type mvar cur-elim (inl lz prev-level unit prev-type star))
            (ap lz lM unit mvar f star)
            cv
            (sum-case-inl lz prev-level lM unit prev-type mvar f prev-elim star)
            (combinator-constant-eq lM lz mvar unit cv star)) in
        let inl-triple = (inl-proof, ((inl lz prev-level unit prev-type star), cv)) in
        let wrapped = (reverse-triples (foldl (fun a => fun triple =>
            let old-proof = (fst triple) in
            let old-inj = (fst (snd triple)) in
            let old-tc = (snd (snd triple)) in
            let new-proof = (trans lM mvar mvar mvar
            (ap cur-level lM cur-type mvar cur-elim (inr lz prev-level unit prev-type old-inj))
            (ap prev-level lM prev-type mvar prev-elim old-inj)
            old-tc
            (sum-case-inr lz prev-level lM unit prev-type mvar f prev-elim old-inj)
            old-proof) in
            (new-proof, ((inr lz prev-level unit prev-type old-inj), old-tc)) :: a
        ) [] prev-triples)) in
        ((inl-triple :: wrapped, cur-elim), (cur-type, cur-level))
        ) (([(last-proof, (star, last-cv))], last-f), (unit, lz)) remaining-cvs) in
        (reverse (foldl (fun acc => fun triple =>
        (fst triple) :: acc) [] (fst (fst result))))
    | _ => []
    end

    schema enum = fun s => match s with
    | [(type-name, [], (Ul lT)),
        (case-name, [(_, level), (mvar, (Ul lM)), (scrut, type-name)], mvar)]
        => (Ok [void, (void-case lM mvar scrut)])
    | [(type-name, [], (Ul lT)),
        (ctor, [], type-name),
        (case-name, [(_, level), (mvar, (Ul lM)), (tc, mvar), (scrut, type-name)], mvar),
        (eq-name, [(_, level), (mvar2, (Ul lM2)), (tc2, mvar2)], _)]
        => (Ok [unit, star, (unit-rec lM mvar tc scrut), (unit-comp lM2 mvar2 tc2)])
    | (type-name, [], (Ul lT)) :: all-rest =>
        let found-params = (foldl (fun acc => fun entry =>
        if (fst acc) == true then acc
        else match entry with
            | (_, [], _) => acc
            | (_, params, _) => (true, params)
            end
        end
        ) (false, [(star, star)]) all-rest) in
        match (snd found-params) with
        | (_, level) :: (mvar, (Ul lM)) :: tc-and-scrut =>
        let vars-info = (foldl (fun acc => fun p =>
            if (fst (fst acc)) == true
            then ((false, (snd (fst acc))), (fst p))
            else ((false, (snd acc) :: (snd (fst acc))), (fst p))
            end
        ) ((true, []), star) tc-and-scrut) in
        let rev-case-vars = (snd (fst vars-info)) in
        let scrut = (snd vars-info) in
        let case-vars = (reverse rev-case-vars) in
        match case-vars with
        | _ :: rest-case-vars =>
            let iat = (build-injs-and-type rest-case-vars) in
            let injs = (fst iat) in
            let coprod-pair = (snd iat) in
            let coprod-type = (fst coprod-pair) in
            let coprod-level = (snd coprod-pair) in
            let elim-arr = (build-elim lM mvar case-vars rest-case-vars) in
            let case-witness = (ap coprod-level lM coprod-type mvar elim-arr scrut) in
            let proofs = (build-proofs lM mvar case-vars rest-case-vars) in
            (Ok (concat [[coprod-type], injs, [case-witness], proofs]))
        | _ => (Error "false ctors") end
        | _ => (Error "bad params") end
    | _ => (Error "unrecognized") end
construct by enum
falsity : Ul lz
falsity-case (lM : level) (M : Ul lM) (scrutinee : falsity) : M
construct by enum
myunit : Ul lz
trivial : myunit
myunit-case (lM : level) (M : Ul lM) (trivial-case : M) (scrutinee : myunit) : M
myunit-case-trivial (lM : level) (M : Ul lM) (trivial-case : M) : eq (myunit-case trivial-case trivial) trivial-case
construct by enum
bool : Ul (lmax lz lz)
true : bool
false : bool
bool-case (lM : level) (M : Ul lM) (true-case false-case : M) (scrutinee : bool) : M
bool-case-true (lM : level) (M : Ul lM) (true-case false-case : M) : eq (bool-case true-case false-case true) true-case
bool-case-false (lM : level) (M : Ul lM) (true-case false-case : M) : eq (bool-case true-case false-case false) false-case
construct by enum
triple : Ul (lmax lz (lmax lz lz))
a : triple
b : triple
c : triple
triple-case (lM : level) (M : Ul lM) (a-case b-case c-case : M) (scrutinee : triple) : M
triple-case-a (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (triple-case a-case b-case c-case a) a-case
triple-case-b (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (triple-case a-case b-case c-case b) b-case
triple-case-c (lM : level) (M : Ul lM) (a-case b-case c-case : M) : eq (triple-case a-case b-case c-case c) c-case
meta
--  todo: cases schema
--  should search through the context for an appropriate eliminator for the input type
-- construct by cases
-- not : to bool bool 
-- not-true : eq (ap not true) false
-- not-false : eq (ap not false) true
end