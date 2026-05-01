postulate
sort : sort
-- universes
level : sort
lz : level
(ls (l : level)) : level
(lmax (l1 : level) (l2 : level)) : level
(Ul (l : level)) : (Ul (ls l))
-- equation types
(eq (l : level) (A : (Ul l)) (B : (Ul l)) (a : A) (b : B)) : (Ul l)
(refl (l : level) (A : (Ul l)) (a : A)) : (eq l A A a a)
(sym (l : level) (A : (Ul l)) (B : (Ul l)) (a : A) (b : B) (e : eq l A B a b)) : (eq l B A b a)
(trans (l : level) (A : (Ul l)) (B : (Ul l)) (C : (Ul l)) (a : A) (b : B) (c : C) (e1 : (eq l A B a b)) (e2 : (eq l B C b c))) : (eq l A C a c)
(cast (l : level) (A : (Ul l)) (B : (Ul l)) (e : eq (ls l) (Ul l) (Ul l) A B) (a : A)) : B
-- function types
(to (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2))) : (Ul (lmax l1 l2))
(ap (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2)) (f : (to l1 l2 A B)) (a : A)) : B
(cong-ap (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2))
         (f : (to l1 l2 A B)) (g : (to l1 l2 A B))
         (a : A) (b : A)
         (ef : (eq (lmax l1 l2) (to l1 l2 A B) (to l1 l2 A B) f g))
         (ea : (eq l1 A A a b))) :
  (eq l2 B B (ap l1 l2 A B f a) (ap l1 l2 A B g b))
-- constant combinator (K) and split combinator for application (S)
(combinator-constant (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2))) : (to l1 (lmax l2 l1) A (to l2 l1 B A))
(combinator-constant-eq (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2)) (x : A) (y : B)) : (eq l1 A A (ap l2 l1 B A (ap l1 (lmax l2 l1) A (to l2 l1 B A) (combinator-constant l1 l2 A B) x) y) x)
(combinator-ap (l1 : level) (l2 : level) (l3 : level) (A : (Ul l1)) (B : (Ul l2)) (C : (Ul l3))) :
  (to (lmax l1 (lmax l2 l3)) (lmax (lmax l1 l2) (lmax l1 l3))
    (to l1 (lmax l2 l3) A (to l2 l3 B C))
    (to (lmax l1 l2) (lmax l1 l3) (to l1 l2 A B) (to l1 l3 A C)))
(combinator-ap-eq (l1 : level) (l2 : level) (l3 : level)
                  (A : (Ul l1)) (B : (Ul l2)) (C : (Ul l3))
                  (f : (to l1 (lmax l2 l3) A (to l2 l3 B C)))
                  (g : (to l1 l2 A B))
                  (x : A)) :
  (eq l3 C C
    (ap l1 l3 A C
      (ap (lmax l1 l2) (lmax l1 l3) (to l1 l2 A B) (to l1 l3 A C)
        (ap (lmax l1 (lmax l2 l3)) (lmax (lmax l1 l2) (lmax l1 l3))
          (to l1 (lmax l2 l3) A (to l2 l3 B C))
          (to (lmax l1 l2) (lmax l1 l3) (to l1 l2 A B) (to l1 l3 A C))
          (combinator-ap l1 l2 l3 A B C)
          f)
        g)
      x)
    (ap l2 l3 B C
      (ap l1 (lmax l2 l3) A (to l2 l3 B C) f x)
      (ap l1 l2 A B g x)))
meta
schema definition =
  fun s => match s with
  | [(f, [], ret),
     (f_eq, [], eq l ret ret f body)]
      => (Ok [body, (refl l ret body)])
  | _ => (Error "invalid definition")
  end
construct by definition
U1 : (Ul (ls (ls lz)))
U1-eq : (eq (ls (ls (ls lz))) (Ul (ls (ls lz))) (Ul (ls (ls lz))) U1 (Ul (ls lz)))
construct by definition
U : U1
U-eq : (eq (ls (ls lz)) U1 U1 U (cast (ls (ls lz)) (Ul (ls lz)) U1 (sym (ls (ls (ls lz))) (Ul (ls (ls lz))) (Ul (ls (ls lz))) U1 (Ul (ls lz)) U1-eq) (Ul lz)))
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
-- data types
void : (Ul lz)
(absurd (Ml : level) (M : (Ul Ml)) (v : void)) : M
unit : (Ul lz)
star : unit
(unit-rec (Ml : level) (M : (Ul Ml)) (star-case : M) (u : unit)) : M
(unit-comp (Ml : level) (M : (Ul Ml)) (star-case : M)) :
  (eq Ml M M (unit-rec Ml M star-case star) star-case)
N : (Ul lz)
zero : N
plus : (to lz (lmax lz lz) N (to lz lz N N))
construct by abstraction
double : (to lz lz N N)
(double-beta (n : N)) : (eq lz N N (ap lz lz N N double n) (ap lz lz N N (ap lz (lmax lz lz) N (to lz lz N N) plus n) n))
end