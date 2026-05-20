-- Approach C: Direct postulation at U level
-- Postulate enum infrastructure directly, use it to witness construct blocks
postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
Code : Sort
El (c : Code) : U
falsity-code : Code
unit-code : Code
triv : El unit-code
bool-code : Code
tt : El bool-code
ff : El bool-code
falsity-elim (M : U) (scrut : El falsity-code) : M
unit-elim (M : U) (triv-case : M) (scrut : El unit-code) : M
unit-beta (M : U) (triv-case : M) : eq M M (unit-elim M triv-case triv) triv-case
bool-elim (M : U) (true-case : M) (false-case : M) (scrut : El bool-code) : M
bool-beta-tt (M : U) (true-case : M) (false-case : M) : eq M M (bool-elim M true-case false-case tt) true-case
bool-beta-ff (M : U) (true-case : M) (false-case : M) : eq M M (bool-elim M true-case false-case ff) false-case
meta
schema enum-from-codes = fun outer => fun s => match s with
  | [(type_name, [], U, _),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar, _)]
    => (Ok [(El falsity-code), (falsity-elim mvar scrut_var)])
  | [(type_name, [], U, _),
     (ctor_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_name, [(mvar2, U), (tc2, mvar2)], _, _)]
    => (Ok [
      (El unit-code),
      triv,
      (unit-elim mvar tc_var scrut_var),
      (unit-beta mvar2 tc2)
    ])
  | [(type_name, [], U, _),
     (true_name, [], type_name, _),
     (false_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _, _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _, _)]
    => (Ok [
      (El bool-code),
      tt,
      ff,
      (bool-elim mvar tc_var fc_var scrut_var),
      (bool-beta-tt mvar2 tc2 fc2),
      (bool-beta-ff mvar3 tc3 fc3)
    ])
  | _ => (Error "unknown enum shape")
  end
construct by enum-from-codes
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
construct by enum-from-codes
unit : U
trivial : unit
unit-case (M : U) (trivial-case : M) (scrutinee : unit) : M
unit-case-trivial (M : U) (trivial-case : M) : eq M M (unit-case M trivial-case trivial) trivial-case
construct by enum-from-codes
bool : U
true : bool
false : bool
bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool) : M
bool-case-true (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case true) true-case
bool-case-false (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case false) false-case
