postulate
U : Sort 
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
-- arrow types
(to (A : U) (B : U)) : U
(ap (A : U) (B : U) (f : (to A B)) (a : A)) : B
(K (A : U) (B : U)) : (to A (to B A))
(S (A : U) (B : U) (C : U)) : (to (to A (to B C)) (to (to A B) (to A C)))
(K-eq (A : U) (B : U) (x : A) (y : B)) : (eq A A (ap B A (ap A (to B A) (K A B) x) y) x)
-- TODO: S-eq
-- natural numbers type
N : U 
plus : (to N (to N N))
meta 
schema abstraction = ?

construct by abstraction
double : (to N N)
(double-beta (n : N)) : (eq N N (ap N N double n) (ap N N (ap N (to N N) plus n) n))

construct by abstraction
triple : (to N N)
(triple-beta (n : N)) : (eq N N (ap N N triple n) (ap N N (ap N (to N N) plus n) (ap N N double n)))
end












