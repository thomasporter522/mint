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
to (A : U) (B : to A (k A U U)) : U
k (X A : U) (a : A) : (to X (k X U A))
to (A : U) (B : to A (k A U U)) : U
k (X A : U) (a : A) : (to X (k X U A))
ap (A : U) (B : to A (k A U U)) (f : to A B) (a : A) : (ap B a)