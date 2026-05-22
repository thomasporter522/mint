postulate 
sort : sort 
U : sort 

eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a

to (A B : U) : U 
ap (A B : U) (f : to A B) (a : A) : B
I (X : U) : to X X
I-eq (X : U) (x : X) : eq (ap I x) x
K (X A : U) : to A (to X A)
K-eq (X A : U) (a : A) (x : X) : eq (ap (ap K a) x) a
S (X A B : U) : (to (to X (to A B)) (to (to X A) (to X B)))
S-eq (X A B : U) (f : to X (to A B)) (a : to X A) (x : X) 
    : eq (ap (ap (ap S f) a) x) (ap (ap f x) (ap a x))

teq (A B : U) : U
trefl (A : U) : teq A A
to-cong (A1 A2 B1 B2 : U) (e1 : teq A1 A2) (e2 : teq B1 B2) : teq (to A1 B1) (to A2 B2)
cast (A B : U) (e : teq A B) : to A B
tto : sort
tap (f : tto) (X : U) : U

forall (f : tto) : U
forall-elim (F : tto) (X : U) : to (forall F) (tap F X)

tI : tto
tI-tap (X : U) : teq (tap tI X) X

tabs-to (A : tto) (B : tto) : tto 
tabs-to-tap (A : tto) (B : tto) (X : U) : teq (tap (tabs-to A B) X) (to (tap A X) (tap B X))

meta 
    schema void-schema = fun _ => fun s => 
        match s with 
        | [_, (_, [(M,_)],_, _)] =>
            (Ok [forall tI, ap (cast (to-cong trefl tI-tap)) (forall-elim tI M)])
        end
construct by void-schema 
void : U 
void-rec (M : U) : to void M

meta 
    schema unit-schema = fun _ => fun s => 
        match s with 
        | [_, _, (_, [(M,_)],_, _), _] =>
            (Ok [
                forall (tabs-to tI tI), 
                ?,
                (forall-elim (tabs-to tI tI) M),
                ?])
        end

construct by unit-schema 
unit : U 
star : unit 
unit-rec (M : U) : to unit (to M M)
unit-iota (M : U) (star-case : M) : eq (ap(ap (unit-rec M) star) star-case) star-case