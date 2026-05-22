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
to (A : U) : sto (sto A U) U
ap (A : U) (B : sto A U) (f : sap (to A) B) (a : A) : sap B a

postulate 
too (A : U) (B : too A (k U)) : ?
k (X A : U) (a : A) : (too X (k A)) : ?
postulate 
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
sap-cong (A1 A2 B1 B2 : U) (f1 : sto A1 B1) (f2 : sto A2 B2) (a1 : A1) (a2 : A2) (e1 : eq f1 f2) (e2 : eq a1 a2) : eq (sap f1 a1) (sap f2 a2)
to-cong (A1 A2 : U) (e1 : eq A1 A2) : eq (to A1) (to A2)
ap-cong (A1 A2 : U) (B1 : sto A1 U) (B2 : sto A2 U)
        (f1 : sap (to A1) B1) (f2 : sap (to A2) B2)
        (a1 : A1) (a2 : A2)
        (e1 : eq f1 f2) (e2 : eq a1 a2)
        : eq (ap f1 a1) (ap f2 a2)
eq-cong (A1 A2 B1 B2 : U) (a1 : A1) (a2 : A2) (b1 : B1) (b2 : B2) (eA : eq A1 A2) (eB : eq B1 B2) (ea : eq a1 a2) (eb : eq b1 b2) : eq (eq a1 b1) (eq a2 b2)

-- todo: conversion

postulate 
slk (X A : U) : sto A (sto X A)
slk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (slk X A) a) x) a
#reduction slk-eq 
lk (X A : U) : sto A (sap (to X) (sap slk A))
lk-eq (X A : U) (a : A) (x : X) : eq (ap (sap (lk X A) a) x) a
#reduction slk-eq 
lid (X : U) : sto X X 
lid-eq (X : U) (x : X) : eq (sap (lid) x) x
#reduction lid-eq 
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq 
lsap (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap slk B))) (a : sap (to X) A) : sto X B
lsap-eq (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap slk B))) (a : sap (to X) A) (x : X) : 
    eq (sap (lsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction lsap-eq
-- clsap (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) : sap (to X) B
-- clsap-eq (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) (x : X) : 
--     eq (ap (clsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
-- #reduction clsap-eq
-- slto (X : U) (A : U) : sto X (sto (sto A U) U)
-- slto-eq (X : U) (A : U) (x : X) : eq (sto (sto A U) U) (sto (sto A U) U) (sap (slto X A) x) (to A)
-- #reduction slto-eq
lto (X : U) (A : sto X U) : sap (to X) (lsto (lsto A (sap slk U)) (sap slk U))
lto-eq (X : U) (A : sto X U) (x : X) : eq (ap (lto X A) x) (to (sap A x))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap slk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) : sap (to X) (lsap B a)
lap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap slk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) (x : X) : 
    eq (ap (lap f a) x) 
        (ap (cast (trans (lsap-eq) (sap-cong (trans cast-eq lto-eq) (sym (cast-eq (trans lsto-eq (sto-cong refl slk-eq)) (ap B x))))) 
                (ap f x))
                (ap a x))
#reduction lap-eq

slap (X : U) (A : U) (B : sto A U)
    (f : sto X (sap (to A) B)) (a : sto X A) : sto X (sap B a)
-- slap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap slk U)))
--     (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) (x : X) : 
--     eq (ap (lap f a) x) 
--         (ap (cast (trans (lsap-eq) (sap-cong (trans cast-eq lto-eq) (sym (cast-eq (trans lsto-eq (sto-cong refl slk-eq)) (ap B x))))) 
--                 (ap f x))
--                 (ap a x))
-- #reduction slap-eq

meta 
  schema definition =
    fun outer => fun s => match s with
    | [(a, _, _, _),
       (a_eq, _, eq _ _ _ body, _)]
        => (Ok [body, (refl)])
    | _ => (Error "invalid definition")
    end

meta 
  schema abstraction = fun outer => fun s => ?

-- construct by abstraction 
-- unit-subelim (unit : U) (star : unit) (t : unit) : sto (sto unit U) U 
-- unit-subelim-beta (unit : U) (star : unit) (t : unit) (M : sto unit U) : 
--   eq (sap (unit-subelim unit star t) M) (sto (sap M star) (sap M t))

-- construct by abstraction 
-- unit-elim (unit : U) (star : unit) : sto unit U 
-- unit-elim-beta (unit : U) (star : unit) (t : unit) : 
--   eq (sap (unit-elim unit star) t) (sap (to (sto unit U)) (unit-subelim unit star t))


meta
  schema void-schema = 
    fun ctx => fun s => 
      (Ok [(sap (to U) lid), lid])

construct by void-schema
void : U
void-rec : sto void (sap (to U) lid)
-- meta 
--   schema unit-schema =
--         fun ctx => fun s =>
--           match s with
--           | [_, (_,_,_,_), _, _] =>
--           (Ok [
--             (pi U (ap (ap abs-to abs-ident) abs-ident)),
--             ?,
--             ?,
--             ?
--             ])
--           | _ => (Error "invalid")
--           end
-- construct by unit-schema
postulate
unit : U
unit-star : unit
unit-rec : sap (to unit) (slap (to (sto unit U)) (sto (ap M star) (ap M t)))
--(lto (ap lk (sto unit U)) ?)

-- pi (ap (ap abs-to (ap abs-const unit)) (ap (ap abs-to abs-ident) abs-ident))
-- unit-rec-eq (M : U) (star-case : M) : 
--   eq M M (ap (ap 
--     (dap unit-rec M)
--      unit-star) star-case) star-case