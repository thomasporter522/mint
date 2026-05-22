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
pre-to (A : U) : sto (sto A U) U
pre-ap (A : U) (B : sto A U) (f : sap (pre-to A) B) (a : A) : sap B a
postulate 
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
sap-cong (A1 A2 B1 B2 : U) (f1 : sto A1 B1) (f2 : sto A2 B2) (a1 : A1) (a2 : A2) (e1 : eq f1 f2) (e2 : eq a1 a2) : eq (sap f1 a1) (sap f2 a2)
to-cong (A1 A2 : U) (e1 : eq A1 A2) : eq (pre-to A1) (pre-to A2)
ap-cong (A1 A2 : U) (B1 : sto A1 U) (B2 : sto A2 U)
        (f1 : sap (pre-to A1) B1) (f2 : sap (pre-to A2) B2)
        (a1 : A1) (a2 : A2)
        (e1 : eq f1 f2) (e2 : eq a1 a2)
        : eq (pre-ap f1 a1) (pre-ap f2 a2)
eq-cong (A1 A2 B1 B2 : U) (a1 : A1) (a2 : A2) (b1 : B1) (b2 : B2) (eA : eq A1 A2) (eB : eq B1 B2) (ea : eq a1 a2) (eb : eq b1 b2) : eq (eq a1 b1) (eq a2 b2)
postulate 
lk (X A : U) : sto A (sto X A)
lk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (lk X A) a) x) a
#reduction lk-eq 
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq 
lsap (X : U) (A : sto X U) (B : U) (f : sap (pre-to X) (lsto A (sap lk B))) (a : sap (pre-to X) A) : sto X B
lsap-eq (X : U) (A : sto X U) (B : U) (f : sap (pre-to X) (lsto A (sap lk B))) (a : sap (pre-to X) A) (x : X) : 
    eq (sap (lsap A B f a) x) (sap (cast lsto-eq (pre-ap f x)) (pre-ap a x))
#reduction lsap-eq
-- clsap (X : U) (A B : sto X U) (f : sap (pre-to X) (lsto A B)) (a : sap (pre-to X) A) : sap (pre-to X) B
-- clsap-eq (X : U) (A B : sto X U) (f : sap (pre-to X) (lsto A B)) (a : sap (pre-to X) A) (x : X) : 
--     eq (ap (clsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
-- #reduction clsap-eq
lto (X : U) (A : sto X U) : sap (pre-to X) (lsto (lsto A (sap lk U)) (sap lk U))
lto-eq (X : U) (A : sto X U) (x : X) : eq (pre-ap (lto X A) x) (pre-to (sap A x))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : sap (pre-to X) (lsto A (sap lk U)))
    (f : sap (pre-to X) (lsap (lto A) B)) (a : sap (pre-to X) A) : sap (pre-to X) (lsap B a)
lap-eq (X : U) (A : sto X U) (B : sap (pre-to X) (lsto A (sap lk U)))
    (f : sap (pre-to X) (lsap (lto A) B)) (a : sap (pre-to X) A) (x : X) : 
    eq (pre-ap (lap f a) x) 
        (pre-ap (cast (trans (lsap-eq) (sap-cong (trans cast-eq lto-eq) (sym (cast-eq (trans lsto-eq (sto-cong refl lk-eq)) (pre-ap B x))))) 
                (pre-ap f x))
                (pre-ap a x))
#reduction lap-eq

meta 
  schema definition =
    fun outer => fun s => match s with
    | [(a, _, _, _),
       (a_eq, _, eq _ _ _ body, _)]
        => (Ok [body, (refl)])
    | _ => (Error "invalid definition")
    end

construct by definition 
to (A : U) (B : sto A U) : U 
to-eq (A : U) (B : sto A U) : eq (to A B) (sap (pre-to A) B)
construct by definition 
ap (A : U) (B : sto A U) (f : to A B) (a : A) : sap B a
ap-eq (A : U) (B : sto A U) (f : to A B) (a : A) : eq (app f a) (pre-ap (cast to-eq f) a)

meta
  schema void-schema = 
    fun ctx => fun s => 
      (Ok [(to U (lk)), lk])

construct by void-schema
void : U
void-rec : to void (pi U (abs-ident))meta 
  schema unit-schema =
        fun ctx => fun s =>
          match s with
          | [_, (_,_,_,_), _, _] =>
          (Ok [
            (pi U (ap (ap abs-to abs-ident) abs-ident)),
            ?,
            ?,
            ?
            ])
          | _ => (Error "invalid")
          end
construct by unit-schema
unit : U
unit-star : unit
unit-rec : pi (ap (ap abs-to (ap abs-const unit)) (ap (ap abs-to abs-ident) abs-ident))
unit-rec-eq (M : U) (star-case : M) : 
  eq M M (ap (ap 
    (dap unit-rec M)
     unit-star) star-case) star-case