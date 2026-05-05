postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Arr (A : U) (B : U) : U
app (A : U) (B : U) (f : Arr A B) (a : A) : B
K (A : U) (B : U) : Arr A (Arr B A)
K-beta (A : U) (B : U) (x : A) (y : B) : eq A A (app B A (app A (Arr B A) (K A B) x) y) x
flip-K (A : U) (B : U) : Arr A (Arr B B)
flip-K-beta (A : U) (B : U) (x : A) (y : B) : eq B B (app B B (app A (Arr B B) (flip-K A B) x) y) y
I (A : U) : Arr A A
I-beta (A : U) (x : A) : eq A A (app A A (I A) x) x
app-cong (A : U) (B : U) (f : Arr A B) (g : Arr A B) (x : A) (e : eq (Arr A B) (Arr A B) f g) : eq B B (app A B f x) (app A B g x)
ForallArr0 : U
inst0 (M : U) (f : ForallArr0) : M
ForallArr1 : U
inst1 (M : U) (f : ForallArr1) : Arr M M
polyId : ForallArr1
polyId-beta (M : U) : eq (Arr M M) (Arr M M) (inst1 M polyId) (I M)
ForallArr2 : U
inst2 (M : U) (f : ForallArr2) : Arr M (Arr M M)
polyK : ForallArr2
polyK-beta (M : U) : eq (Arr M (Arr M M)) (Arr M (Arr M M)) (inst2 M polyK) (K M M)
polyFlipK : ForallArr2
polyFlipK-beta (M : U) : eq (Arr M (Arr M M)) (Arr M (Arr M M)) (inst2 M polyFlipK) (flip-K M M)
meta
schema enum = fun s => match s with | [(type_name, [], U), (case_name, [(mvar, U), (scrut_var, type_name)], mvar)] => (Ok [ForallArr0, (inst0 mvar scrut_var)]) | [(type_name, [], U), (ctor_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar), (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)] => (Ok [ForallArr1, polyId, (app mvar mvar (inst1 mvar scrut_var) tc_var), (trans mvar2 (app mvar2 mvar2 (inst1 mvar2 polyId) tc_var2) (app mvar2 mvar2 (I mvar2) tc_var2) tc_var2 (app-cong mvar2 mvar2 (inst1 mvar2 polyId) (I mvar2) tc_var2 (polyId-beta mvar2)) (I-beta mvar2 tc_var2))]) | [(type_name, [], U), (true_name, [], type_name), (false_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar), (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _), (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)] => (Ok [ForallArr2, polyK, polyFlipK, (app mvar mvar (app mvar (Arr mvar mvar) (inst2 mvar scrut_var) tc_var) fc_var), (trans mvar2 (app mvar2 mvar2 (app mvar2 (Arr mvar2 mvar2) (inst2 mvar2 polyK) tc2) fc2) (app mvar2 mvar2 (app mvar2 (Arr mvar2 mvar2) (K mvar2 mvar2) tc2) fc2) tc2 (app-cong mvar2 mvar2 (app mvar2 (Arr mvar2 mvar2) (inst2 mvar2 polyK) tc2) (app mvar2 (Arr mvar2 mvar2) (K mvar2 mvar2) tc2) fc2 (app-cong mvar2 (Arr mvar2 mvar2) (inst2 mvar2 polyK) (K mvar2 mvar2) tc2 (polyK-beta mvar2))) (K-beta mvar2 mvar2 tc2 fc2)), (trans mvar3 (app mvar3 mvar3 (app mvar3 (Arr mvar3 mvar3) (inst2 mvar3 polyFlipK) tc3) fc3) (app mvar3 mvar3 (app mvar3 (Arr mvar3 mvar3) (flip-K mvar3 mvar3) tc3) fc3) fc3 (app-cong mvar3 mvar3 (app mvar3 (Arr mvar3 mvar3) (inst2 mvar3 polyFlipK) tc3) (app mvar3 (Arr mvar3 mvar3) (flip-K mvar3 mvar3) tc3) fc3 (app-cong mvar3 (Arr mvar3 mvar3) (inst2 mvar3 polyFlipK) (flip-K mvar3 mvar3) tc3 (polyFlipK-beta mvar3))) (flip-K-beta mvar3 mvar3 tc3 fc3))]) | _ => (Error "enum: unsupported number of constructors") end
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

