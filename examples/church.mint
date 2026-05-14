postulate
sort : sort
U : U
-- function types
to (A B : U) : U
ap (A B : U) (f : to A B) (a : A) : B
pi (A : U) (B : to A U) : U
dap (A : U) (B : to A U) (f : pi A B) (a : A) : ap B a
-- equations
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
-- todo: use a unified eq eliminator
cast (A B : U) : to (eq A B) (to A B)
sym (A B : U) (a : A) (b : B) : to (eq a b) (eq b a)
trans (A B C : U) (a : A) (b : B) (c : C) : to (eq a b) (to (eq b c) (eq a c))

cong-ap (A B : U)
  (f : to A B) (g : to A B)
  (a : A) (b : A) 
  : to (eq f g) 
    (to (eq a b) 
      (eq (ap f a) (ap g b)))
cong-to (A1 B1 A2 B2 : U)
  (eA : eq A1 A2) (eB : eq B1 B2)
  : eq (to A1 B1) (to A2 B2)

abs-const (X A : U) 
  : to A (to X A)
abs-const-eq (X A : U) 
  (x : X) (a : A) 
  : eq (ap (ap (abs-const) a) x) a
abs-ident (X : U) 
  : to X X
abs-ident-eq (X : U) 
  (x : X)
  : eq (ap (abs-ident) x) x
abs-ap (X A B : U) 
  : to (to X (to A B)) (to (to X A) (to X B))
abs-ap-eq (X A B : U) 
  (f : to X (to A B)) 
  (a : to X A) 
  (x : X) 
  : eq (ap (ap (ap (abs-ap) f) a) x) (ap (ap f x) (ap a x))
abs-to (X : U)
  : to (to X U) (to (to X U) (to X U))
abs-to-eq (X : U) (A : to X U) (B : to X U) 
  (x : X) 
  : eq (ap (ap (ap (abs-to) A) B) x) (to (ap A x) (ap B x))
abs-eq (X : U)
  : to (to X U) (to (to X U) (to X U))
abs-eq-eq (X : U) (A : to X U) (B : to X U) 
  (x : X) 
  : eq (ap (ap (ap (abs-eq) A) B) x) (eq (ap A x) (ap B x))

meta 
    schema void-schema = 
        fun ctx => fun s => 
          (Ok [(pi U (abs-ident)), abs-ident])
construct by void-schema
void : U
void-rec : to void (pi U (abs-ident))
meta 
    coerce silly-case = fun ctx => fun expected => fun found => fun contents => 
      (Ok (ap (ap cast ?) contents))
    schema unit-schema = 
        fun ctx => fun s => 
          match s with 
          | [_, (_,_,_), _, _] => 
          (Ok [
            ?,
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
  -- eq ap ...
  ap (dap unit-rec M) unit-star
  -- ... star-case star-case

-- doesn't work because the motive needs to be abstractible
-- construct by unit-schema
-- unit : U
-- unit-star : unit
-- unit-rec (M : U) : to unit (to M M)
-- unit-rec-eq (M : U) (star-case : M) : eq (ap (ap (unit-rec M) unit-star) star-case) star-case
