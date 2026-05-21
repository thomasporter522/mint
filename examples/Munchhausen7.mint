-- Based on section 7 of "The Münchhausen Method in Type Theory"
postulate
sort : sort
U : U
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
meta 
    newtag #reduction
    schema definition =
        fun outer => fun s => match s with
        | [(a, _, _, _),
            (a_eq, _, eq _ _ _ body, _)]
            => (Ok [body, (refl)])
        | _ => (Error "invalid definition")
    end
postulate 
fam (A : U) : U 
apf (A : U) (f : fam A) (a : A) : U
pi (A : U) : fam (fam A)
ap (A : U) (B : fam A) (f : apf (pi A) B) (a : A) : apf B a
Kf (X A : U) : fam X
Kf-beta (X A : U) (x : X) : eq (apf (Kf A) x) A
#reduction Kf-beta
construct by definition
to (A B : U) : U
to-beta (A B : U) : eq (to A B) (apf (pi A) (Kf B))
#reduction to-beta
postulate 
cast (A B : U) (e : eq A B) (a : A) : B

Sto (X : U) (A B : fam X) : fam X 
Sto-beta (X : U) (A B : fam X) (x : X) : eq (apf (Sto A B) x) (to (apf A x) (apf B x))
#reduction Sto-beta

postulate
K (A : U) (B : fam A) : apf (pi A) (Sto B (Kf A))
K-beta (A : U) (B : fam A) (a : A) (b : apf B a) : 
    eq (ap (cast to-beta (cast Sto-beta (ap (K A B) a))) b) a

