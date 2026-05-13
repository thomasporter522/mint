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
pi (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) : Ul (lmax l1 l2)
dap (l1 l2 : level) (A : Ul l1) (B : to A (Ul l2)) (f : pi A B) (a : A) : ap B a
-- equations
eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) : Ul (lmax l1 l2)
refl (l : level) (A : Ul l) (a : A) : eq a a
cast (l : level) (A B : Ul l) (e : eq A B) (a : A) : B
eq-ind-M-B (l Ml : level) (A : Ul l) (a : A) : to A (Ul l)
eq-ind-M-B-eq (l Ml : level) (A : Ul l) (a b : A) : eq (ap (eq-ind-M-B Ml A a) b) (to (eq a b) (Ul Ml)) 
eq-ind (l Ml : level) (A : Ul l) (a : A)
  (M : pi A (eq-ind-M-B Ml A a))
  (base : ap (cast (eq-ind-M-B-eq) (dap M a)) ?)
  (base : dap M a)
  : dap M ?