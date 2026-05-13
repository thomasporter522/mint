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
--     (pB : to A (Ul pl))
--     (p : pi A pB)
--     (pa : dap p a)
--     : dap p b
eq-prop (l pl : level) (A : Ul l) (a b : A)
    (e : eq a b)
    (pB : to A (Ul pl))
    (p : dto A pB)
    (pa : dap p a)
    : dap p b

abs-const (l1 l2 : level) 
  (A : Ul l1) (B : Ul l2) 
  : to A (to B A)
abs-const-eq (l1 l2 : level) 
  (A : Ul l1) (B : Ul l2) 
  (x : A) (y : B) 
  : eq (ap (ap (abs-const) x) y) x
abs-ident (l: level) 
  (A : Ul l)
  : to A A
abs-ident-eq (l : level) 
  (A : Ul l)
  (x : A)
  : eq (ap (abs-ident) x) x


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
    | [(a, _, _),
       (a_eq, _, eq _ _ _ _ _ body)]
        => (Ok [body, (refl)])
    | _ => (Error "invalid definition")
    end
-- insert any constructions (not postulates) you wish
construct by definition
cast (l : level) (A B : Ul l) (e : eq A B) (a : A) : B
cast-pf (l : level) (A B : Ul l) (e : eq A B) (a : A) : eq B (cast e a) 
    (eq-prop dabs-ident a)

-- sym (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) (e : eq a b) : eq b a
-- sym-eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) (e : eq a b) : eq (eq l2 l1 B A b a) (sym e)
--     ?
