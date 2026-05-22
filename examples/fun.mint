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
sto (A B : U) : U 
sap (A B : U) (f : sto A B) (a : A) : B
to (A : U) (B : sto A U) : U
ap (A : U) (B : sto A U) (f : (to A B)) (a : A) : sap B a
postulate 
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
sap-cong (A1 A2 B1 B2 : U) (f1 : sto A1 B1) (f2 : sto A2 B2) (a1 : A1) (a2 : A2) (e1 : eq f1 f2) (e2 : eq a1 a2) : eq (sap f1 a1) (sap f2 a2)
to-cong (A1 A2 : U) (B1 : sto A1 U) (B2 : sto A2 U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (to A1 B1) (to A2 B2)
ap-cong (A1 A2 : U) (B1 : sto A1 U) (B2 : sto A2 U)
        (f1 : to A1 B1) (f2 : to A2 B2)
        (a1 : A1) (a2 : A2)
        (e1 : eq f1 f2) (e2 : eq a1 a2)
        : eq (ap f1 a1) (ap f2 a2)
eq-cong (A1 A2 B1 B2 : U) (a1 : A1) (a2 : A2) (b1 : B1) (b2 : B2) (eA : eq A1 A2) (eB : eq B1 B2) (ea : eq a1 a2) (eb : eq b1 b2) : eq (eq a1 b1) (eq a2 b2)
postulate 
lk (X A : U) : sto A (sto X A)
lk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (lk X A) a) x) a
#reduction lk-eq 
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq 
lsap (X : U) (A : sto X U) (B : U) (f : to X (lsto A (sap lk B))) (a : to X A) : sto X B
lsap-eq (X : U) (A : sto X U) (B : U) (f : to X (lsto A (sap lk B))) (a : to X A) (x : X) : 
    eq (sap (lsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction lsap-eq
-- clsap (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) : sap (to X) B
-- clsap-eq (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) (x : X) : 
--     eq (ap (clsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
-- #reduction clsap-eq
lto (X : U) (A : sto X U) (B : to X (lsto A (sap lk U))) : to X (lsto (lsto A (sap lk U)) (sap lk U))
lto-eq (X : U) (A : sto X U) (B : to X (lsto A (sap lk U))) (x : X) : eq (ap (lto A B) x) (to (sap A x) (cast (trans lsto-eq (sto-cong refl lk-eq)) (ap B x)))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : to X (lsto A (sap lk U)))
    (f : to X (cast ? (lto A B)))
    (a : sap (to X) A) : sap (to X) (lsap B a)
-- lap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
--     (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) (x : X) : 
--     eq (ap (lap f a) x) 
--         (ap (cast (trans (lsap-eq) (sap-cong (trans cast-eq lto-eq) (sym (cast-eq (trans lsto-eq (sto-cong refl lk-eq)) (ap B x))))) 
--                 (ap f x))
--                 (ap a x))
-- #reduction lap-eq
