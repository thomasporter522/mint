postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Arr (A : U) (B : U) : U
app (A : U) (B : U) (f : Arr A B) (a : A) : B
const (A : U) (B : U) (b : B) : Arr A B
const-beta (A : U) (B : U) (b : B) (a : A) : eq B B (app A B (const A B b) a) b
Void : U
absurd (M : U) (v : Void) : M
Unit : U
star : Unit
unit-rec (M : U) (star-case : M) (u : Unit) : M
unit-comp (M : U) (star-case : M) : eq M M (unit-rec M star-case star) star-case
Either (A : U) (B : U) : U
inl (A : U) (B : U) (a : A) : Either A B
inr (A : U) (B : U) (b : B) : Either A B
either (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (e : Either A B) : M
either-inl (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (a : A) : eq M M (either A B M f g (inl A B a)) (app A M f a)
either-inr (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (b : B) : eq M M (either A B M f g (inr A B b)) (app B M g b)
app-cong (A : U) (B : U) (f : Arr A B) (g : Arr A B) (x : A) (e : eq (Arr A B) (Arr A B) f g) : eq B B (app A B f x) (app A B g x)
meta
schema enum = fun s => match s with | [(type_name, [], U), (case_name, [(mvar, U), (scrut_var, type_name)], mvar)] => (Ok [Void, (absurd mvar scrut_var)]) | _ => (Error "TODO: generic case not implemented") end
construct by enum
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
end

