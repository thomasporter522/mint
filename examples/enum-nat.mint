postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Nat : U
zero : Nat
succ (n : Nat) : Nat
Vec (A : U) (n : Nat) : U
vnil (A : U) : Vec A zero
vcons (A : U) (n : Nat) (head : A) (tail : Vec A n) : Vec A (succ n)
Enum (n : Nat) : U
ezero (n : Nat) : Enum (succ n)
esucc (n : Nat) (i : Enum n) : Enum (succ n)
enum-elim (n : Nat) (M : U) (cases : Vec M n) (e : Enum n) : M
enum-beta-zero (n : Nat) (M : U) (head : M) (tail : Vec M n) : eq M M (enum-elim (succ n) M (vcons M n head tail) (ezero n)) head
enum-beta-succ (n : Nat) (M : U) (head : M) (tail : Vec M n) (i : Enum n) : eq M M (enum-elim (succ n) M (vcons M n head tail) (esucc n i)) (enum-elim n M tail i)
enum-absurd (M : U) (e : Enum zero) : M
meta
n0 = zero
n1 = (succ zero)
n2 = (succ (succ zero))
schema enum = fun s => match s with | [(type_name, [], U), (case_name, [(mvar, U), (scrut_var, type_name)], mvar)] => (Ok [(Enum n0), (enum-absurd mvar scrut_var)]) | [(type_name, [], U), (ctor_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar), (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)] => (Ok [(Enum n1), (ezero n0), (enum-elim n1 mvar (vcons mvar n0 tc_var (vnil mvar)) scrut_var), (enum-beta-zero n0 mvar2 tc_var2 (vnil mvar2))]) | [(type_name, [], U), (true_name, [], type_name), (false_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar), (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _), (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)] => (Ok [(Enum n2), (ezero n1), (esucc n1 (ezero n0)), (enum-elim n2 mvar (vcons mvar n1 tc_var (vcons mvar n0 fc_var (vnil mvar))) scrut_var), (enum-beta-zero n1 mvar2 tc2 (vcons mvar2 n0 fc2 (vnil mvar2))), (trans mvar3 (enum-elim n2 mvar3 (vcons mvar3 n1 tc3 (vcons mvar3 n0 fc3 (vnil mvar3))) (esucc n1 (ezero n0))) (enum-elim n1 mvar3 (vcons mvar3 n0 fc3 (vnil mvar3)) (ezero n0)) fc3 (enum-beta-succ n1 mvar3 tc3 (vcons mvar3 n0 fc3 (vnil mvar3)) (ezero n0)) (enum-beta-zero n0 mvar3 fc3 (vnil mvar3)))]) | _ => (Error "enum: unsupported (expected 0, 1, or 2 constructors)") end
construct by enum
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
construct by enum
unit : U
trivial : unit
unit-case (M : U) (trivial-case : M) (scrutinee : unit) : M
unit-case-trivial (M : U) (trivial-case : M) : eq M M (unit-case M trivial-case trivial) trivial-case
construct by enum
bool : U
true : bool
false : bool
bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool) : M
bool-case-true (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case true) true-case
bool-case-false (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case false) false-case
end

