postulate
sort : sort
level : sort
level-zero : level
level-suc (l : level) : level
U (l : level) : U (level-suc l)
U : sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
to (A : U) (B : U) : U
ap (A : U) (B : U) (f : to A B) (a : A) : B
cong-ap (A : U) (B : U) (f : to A B) (g : to A B) (a : A) (b : A) (ef : eq (to A B) (to A B) f g) (ea : eq A A a b) : eq B B (ap A B f a) (ap A B g b)
K (A : U) (B : U) : to A (to B A)
S (A : U) (B : U) (C : U) : to (to A (to B C)) (to (to A B) (to A C))
K-eq (A : U) (B : U) (x : A) (y : B) : eq A A (ap B A (ap A (to B A) (K A B) x) y) x
S-eq (A : U) (B : U) (C : U) (f : to A (to B C)) (g : to A B) (x : A) : eq C C (ap A C (ap (to A B) (to A C) (ap (to A (to B C)) (to (to A B) (to A C)) (S A B C) f) g) x) (ap B C (ap A (to B C) f x) (ap A B g x))
N : U
zero : N
plus : to N (to N N)
pi (A : U) (B : to A U) : U
ap-pi (A : U) (B : to A U) (f : pi A B) (a : A) : ap A U B a
meta
abs = fun x => fun e => fun A => fun B => if e == x then ((ap (to A (to A A)) (to A A) (ap (to A (to (to A A) A)) (to (to A (to A A)) (to A A)) (S A (to A A) A) (K A (to A A))) (K A A)), (trans A (ap A A (ap (to A (to A A)) (to A A) (ap (to A (to (to A A) A)) (to (to A (to A A)) (to A A)) (S A (to A A) A) (K A (to A A))) (K A A)) x) (ap (to A A) A (ap A (to (to A A) A) (K A (to A A)) x) (ap A (to A A) (K A A) x)) x (S-eq A (to A A) A (K A (to A A)) (K A A) x) (K-eq A (to A A) x (ap A (to A A) (K A A) x)))) else match e with | (ap Aprime Bprime f a) => let f-res = (abs x f A (to Aprime B)) in let a-res = (abs x a A Aprime) in let fw = (fst f-res) in let fp = (snd f-res) in let aw = (fst a-res) in let ap2 = (snd a-res) in let witness = (ap (to A Aprime) (to A B) (ap (to A (to Aprime B)) (to (to A Aprime) (to A B)) (S A Aprime B) fw) aw) in let proof = (trans B (ap A B witness x) (ap Aprime B (ap A (to Aprime B) fw x) (ap A Aprime aw x)) (ap Aprime B f a) (S-eq A Aprime B fw aw x) (cong-ap Aprime B (ap A (to Aprime B) fw x) f (ap A Aprime aw x) a fp ap2)) in (witness, proof) | _ => ((ap B (to A B) (K B A) e), (K-eq B A e x)) end end
schema abstraction = fun s => match s with | [(f, [], (to A B)), (_, [(x, _)], (eq _ _ (ap _ _ f x) body))] => let result = (abs x body A B) in (Ok [(fst result), (snd result)]) | _ => (Error "abstraction: expected (f : to A B) and (f-beta (x : A) : eq B B (ap A B f x) body)") end
construct by abstraction
double : to N N
double-beta (n : N) : eq N N (ap N N double n) (ap N N (ap N (to N N) plus n) n)
construct by abstraction
triple : to N N
triple-beta (n : N) : eq N N (ap N N triple n) (ap N N (ap N (to N N) plus n) (ap N N double n))
construct by abstraction
aptwice : to (to N N) N
aptwice-beta (f : to N N) : eq N N (ap (to N N) N aptwice f) (ap N N f (ap N N f zero))
end

