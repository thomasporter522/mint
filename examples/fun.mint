-- Based on section 7 of "The Münchhausen Method in Type Theory"
postulate
sort : sort
U : U
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
cast (A B : U) (e : eq A B) (a : A) : B
trans (A B C : U) (a : A) (b : B) (c : C) (e1 : eq a b) (e2 : eq b c) : eq a c
meta 
    newtag #reduction
postulate 
sto (A B : U) : U 
sap (A B : U) (f : sto A B) (a : A) : B
to (A : U) : sto (sto A U) U
ap (A : U) (B : sto A U) (f : sap (to A) B) (a : A) : sap B a
postulate 
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
-- eq-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (eq A1 B1) (eq A2 B2)
postulate 
lk (X A : U) : sto A (sto X A)
lk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (lk X A) a) x) a
#reduction lk-eq 
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq 
slsap (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) : sto X B
slsap-eq (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) (x : X) : 
    eq (sap (slsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction slsap-eq
lsap (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) : sap (to X) B
lsap-eq (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) (x : X) : 
    eq (ap (lsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction lsap-eq
lto (X : U) (A : sto X U) : sap (to X) (lsto (lsto A (sap lk U)) (sap lk U))
lto-eq (X : U) (A : sto X U) (x : X) : eq (ap (lto X A) x) (to (sap A x))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (slsap (lto A) B)) (a : sap (to X) A) : sap (to X) (slsap B a)
lap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (slsap (lto A) B)) (a : sap (to X) A) (x : X) : 
    eq (sap U (cast (trans lsto-eq (sto-cong refl lk-eq)) (ap B x)) (ap a x)) (ap (lap A B f a) x) 
        (ap 
            -- (cast (trans (slsap-eq) ?) (ap f x))
        (ap a x))

-- ? : eq (sap (sap (lsto A (sap (lk X U) U)) x) (sap (sap (lk X U) U) x) (cast (lsto-eq (lsto A (sap (lk X U) U)) (sap (lk X U) U) x) (ap (lto A) x)) (ap X (lsto A (sap (lk X U) U)) B x)) 
--     (sap (to (sap A x)) ?)hole
