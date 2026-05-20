postulate
sort : sort
-- universe levels
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
-- function types
to (l1 l2 : level) (A : Ul l1) (B : Ul l2) : Ul (lmax l1 l2)
ap (l1 l2 : level) (A : Ul l1) (B : Ul l2) (f : to A B) (a : A) : B
dto (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) : Ul (lmax l1 l2)
dap (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) (f : dto A B) (a : A) : ap B a
-- equations
eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) : Ul (lmax l1 l2)

-- direction 1
-- option 1
refl (l : level) (A : Ul l) (a : A) : eq a a 
-- option 2
-- ...
-- eq-intro-b (l1 l2 pl : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) : to (to A (Ul pl)) ?
-- eq-intro-b-eq (l1 l2 pl : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) (pB : to A (Ul pl)) : eq (ap (eq-intro-b l1 l2 pl A B a b) pB) 
--     (pi (pi A pB) eq-intro-b-b)
-- eq-intro (l1 l2 pl : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) 
--     (o : pi (to A (Ul pl)) (eq-intro-b l1 l2 pl A B a b))
--     : eq a b

-- direction 2
-- doesn't type check because of heterogeneity
-- eq-elim (l1 l2 pl : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) 
--     (e : eq a b)
--     (p : to A (Ul pl))
--     (pa : ap p a)
--     : ap p b
subst (l pl : level) (A : Ul l) (a b : A)
    (e : eq a b)
    (p : to A (Ul pl))
    (pa : ap p a)
    : ap p b

cast (l : level) (A B : Ul l) (e : eq A B) (a : A) : B


abs-const (l1 l2 : level) 
  (X : Ul l1) (A : Ul l2) 
  : to A (to X A)
abs-const-eq (l1 l2 : level) 
  (X : Ul l1) (A : Ul l2) 
  (x : X) (a : A) 
  : eq (ap (ap (abs-const) a) x) a
abs-ident (l: level) 
  (X : Ul l)
  : to X X
abs-ident-eq (l : level) 
  (X : Ul l)
  (x : X)
  : eq (ap (abs-ident) x) x
abs-ap (l1 l2 l3 : level) 
  (X : Ul l1) (A : Ul l2) (B : Ul l3) 
  : to (to X (to A B)) (to (to X A) (to X B))
abs-ap-eq (l1 l2 l3 : level) 
  (X : Ul l1) (A : Ul l2) (B : Ul l3) 
  (f : to X (to A B)) 
  (a : to X A) 
  (x : X) 
  : eq (ap (ap (ap (abs-ap) f) a) x) (ap (ap f x) (ap a x))
abs-eq (l1 l2 l3 : level) 
  (X : Ul l1)
  : to (to X (Ul l2)) (to (to X (Ul l3)) (to X (Ul (lmax l2 l3))))
abs-eq-eq (l1 l2 l3 : level) 
  (X : Ul l1) (A : to X (Ul l2)) (B : to X (Ul l3)) 
  (x : X) 
  : eq (ap (ap (ap (abs-eq) A) B) x) (eq (ap A x) (ap B x))
dabs-ident (l: level) 
  (A : Ul l)
  : dto A (ap (abs-const) A)
dabs-ident-eq (l : level) 
  (A : Ul l)
  (x : A)
  : eq (dap (dabs-ident) x) x
meta
  schema definition =
    fun outer => fun s => match s with
    | [(a, _, _, _),
       (a_eq, _, eq _ _ _ _ _ body, _)]
        => (Ok [body, (refl)])
    | _ => (Error "invalid definition")
    end
-- insert any constructions (not postulates) you wish
construct by definition
sym (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) (e : eq a b) : eq b a
sym-eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) (e : eq a b) : eq (eq l2 l1 B A b a) (sym e) 
  cast
    -- (cast 
    -- ? 
    -- (subst a b e (ap (ap (abs-eq l1 l1 l2 A) (abs-ident A)) (ap (abs-const A A) a)) (refl a)))
    