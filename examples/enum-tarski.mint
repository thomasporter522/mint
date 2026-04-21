-- Approach 3: Tarski-style universe with codes
--
-- Postulate a universe of "codes" (Code : Sort) with a decoding function
-- (El : Code -> U). Postulate specific enum codes (void-c, unit-c, bool-c)
-- with their decoders, constructors, eliminators, and beta rules.
--
-- This is more structured than Approach 2: the codes and El function
-- provide an explicit "universe of enum types" layer. New enum types
-- are added by extending the code universe, not by adding ad-hoc types.
--
-- Soundness: Same as Approach 2 — the decoded types have standard
-- enum semantics. The Code/El layer adds no logical strength;
-- it's purely organizational. Validated by the standard set-theoretic
-- model of a Tarski universe.
--
-- Minimality: Code/El add 2 postulates beyond Approach 2.
-- Trade-off: cleaner structure vs. slightly larger postulate set.
postulate
Sort : Sort
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
-- Tarski universe of enum types
Code : Sort
(El (c : Code)) : U
-- Void code (0 elements)
void-c : Code
(void-elim (M : U) (v : (El void-c))) : M
-- Unit code (1 element)
unit-c : Code
unit-val : (El unit-c)
(unit-elim (M : U) (unit-val-case : M) (u : (El unit-c))) : M
(unit-beta (M : U) (unit-val-case : M)) :
  (eq M M (unit-elim M unit-val-case unit-val) unit-val-case)
-- Bool code (2 elements)
bool-c : Code
yes-val : (El bool-c)
no-val : (El bool-c)
(bool-elim (M : U) (yes-case : M) (no-case : M) (b : (El bool-c))) : M
(bool-yes-beta (M : U) (yes-case : M) (no-case : M)) :
  (eq M M (bool-elim M yes-case no-case yes-val) yes-case)
(bool-no-beta (M : U) (yes-case : M) (no-case : M)) :
  (eq M M (bool-elim M yes-case no-case no-val) no-case)
meta
schema enum = fun s => match s with
  -- 0 constructors: map to El void-c
  | [(type_name, [], U),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar)]
    => (Ok [(El void-c), (void-elim mvar scrut_var)])

  -- 1 constructor: map to El unit-c
  | [(type_name, [], U),
     (ctor_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)]
    => (Ok [
      (El unit-c),
      unit-val,
      (unit-elim mvar tc_var scrut_var),
      (unit-beta mvar2 tc_var2)
    ])

  -- 2 constructors: map to El bool-c
  | [(type_name, [], U),
     (true_name, [], type_name),
     (false_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)]
    => (Ok [
      (El bool-c),
      yes-val,
      no-val,
      (bool-elim mvar tc_var fc_var scrut_var),
      (bool-yes-beta mvar2 tc2 fc2),
      (bool-no-beta mvar3 tc3 fc3)
    ])

  | _ => (Error "enum: unsupported number of constructors (expected 0, 1, or 2)")
  end
construct by enum
  falsity : U
  (falsity-case (M : U) (scrutinee : falsity)) : M
construct by enum
  unit : U
  trivial : unit
  (unit-case (M : U) (trivial-case : M) (scrutinee : unit)) : M
  (unit-case-trivial (M : U) (trivial-case : M)) :
    (eq M M (unit-case M trivial-case trivial) trivial-case)
construct by enum
  bool : U
  true : bool
  false : bool
  (bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool)) : M
  (bool-case-true (M : U) (true-case : M) (false-case : M)) :
    (eq M M (bool-case M true-case false-case true) true-case)
  (bool-case-false (M : U) (true-case : M) (false-case : M)) :
    (eq M M (bool-case M true-case false-case false) false-case)
end
