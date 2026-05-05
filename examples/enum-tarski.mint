postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
Code : Sort
El (c : Code) : U
void-c : Code
void-elim (M : U) (v : El void-c) : M
unit-c : Code
unit-val : El unit-c
unit-elim (M : U) (unit-val-case : M) (u : El unit-c) : M
unit-beta (M : U) (unit-val-case : M) : eq M M (unit-elim M unit-val-case unit-val) unit-val-case
bool-c : Code
yes-val : El bool-c
no-val : El bool-c
bool-elim (M : U) (yes-case : M) (no-case : M) (b : El bool-c) : M
bool-yes-beta (M : U) (yes-case : M) (no-case : M) : eq M M (bool-elim M yes-case no-case yes-val) yes-case
bool-no-beta (M : U) (yes-case : M) (no-case : M) : eq M M (bool-elim M yes-case no-case no-val) no-case
meta
schema enum = fun s => match s with | [(type_name, [], U), (case_name, [(mvar, U), (scrut_var, type_name)], mvar)] => (Ok [(El void-c), (void-elim mvar scrut_var)]) | [(type_name, [], U), (ctor_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar), (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)] => (Ok [(El unit-c), unit-val, (unit-elim mvar tc_var scrut_var), (unit-beta mvar2 tc_var2)]) | [(type_name, [], U), (true_name, [], type_name), (false_name, [], type_name), (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar), (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _), (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)] => (Ok [(El bool-c), yes-val, no-val, (bool-elim mvar tc_var fc_var scrut_var), (bool-yes-beta mvar2 tc2 fc2), (bool-no-beta mvar3 tc3 fc3)]) | _ => (Error "enum: unsupported number of constructors (expected 0, 1, or 2)") end
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

