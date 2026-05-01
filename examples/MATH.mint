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
(combinator-constant (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2))) : (to l1 (lmax l2 l1) A (to l2 l1 B A))
(combinator-constant-eq (l1 : level) (l2 : level) (A : (Ul l1)) (B : (Ul l2)) (x : A) (y : B)) : (eq l1 A A (ap l2 l1 B A (ap l1 (lmax l2 l1) A (to l2 l1 B A) (combinator-constant l1 l2 A B) x) y) x)
combinator-ap : ?
combinator-ap-eq : ?
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
end
