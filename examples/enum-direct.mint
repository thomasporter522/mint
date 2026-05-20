-- Approach 2: Direct enum postulation
--
-- Postulate specific enum types (Void, Unit, Bool) directly with
-- their constructors, eliminators, and beta rules.
-- The schema maps construct declarations to these postulated types.
--
-- This is the simplest approach: postulate exactly the types you need.
-- The construct blocks become trivially witnessed by the postulated terms.
--
-- Soundness: The postulates are exactly the rules of standard enum types.
-- They are validated by any set-theoretic model (Void = empty set,
-- Unit = singleton, Bool = two-element set). No coercion, no type-level
-- computation. Manifestly consistent.
--
-- Minimality: Each postulate is necessary — the types, constructors,
-- eliminators, and beta rules are the minimal interface of an enum type.
-- However, the approach is not GENERIC — extending to 3+ constructors
-- requires adding new postulates for each arity.
postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
Void : U
absurd (M : U) (v : Void) : M
Unit : U
tt : Unit
unit-rec (M : U) (tt-case : M) (u : Unit) : M
unit-comp (M : U) (tt-case : M) : eq M M (unit-rec M tt-case tt) tt-case
Bool : U
yes : Bool
no : Bool
bool-rec (M : U) (yes-case : M) (no-case : M) (b : Bool) : M
bool-comp-yes (M : U) (yes-case : M) (no-case : M) : eq M M (bool-rec M yes-case no-case yes) yes-case
bool-comp-no (M : U) (yes-case : M) (no-case : M) : eq M M (bool-rec M yes-case no-case no) no-case
meta
schema enum = fun outer => fun s => match s with
  -- 0 constructors: map to Void
  | [(type_name, [], U, _),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar, _)]
    => (Ok [Void, (absurd mvar scrut_var)])

  -- 1 constructor: map to Unit
  | [(type_name, [], U, _),
     (ctor_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _, _)]
    => (Ok [
      Unit,
      tt,
      (unit-rec mvar tc_var scrut_var),
      (unit-comp mvar2 tc_var2)
    ])

  -- 2 constructors: map to Bool
  | [(type_name, [], U, _),
     (true_name, [], type_name, _),
     (false_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _, _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _, _)]
    => (Ok [
      Bool,
      yes,
      no,
      (bool-rec mvar tc_var fc_var scrut_var),
      (bool-comp-yes mvar2 tc2 fc2),
      (bool-comp-no mvar3 tc3 fc3)
    ])

  | _ => (Error "enum: unsupported number of constructors (expected 0, 1, or 2)")
  end
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
