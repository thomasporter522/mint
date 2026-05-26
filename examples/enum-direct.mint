-- enum-direct.mint — ported from main.
-- Postulates Void/Unit/Bool directly with their eliminators + beta
-- rules; the schema maps each construct shape (2 / 4 / 6 decls) onto
-- the corresponding postulate.

postulate
U : U
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
end

meta
(* schema enum (main meta): pattern-match by signature shape and emit
   witnesses against the postulated Void / Unit / Bool. The param
   names (mvar, tc_var, ...) are pulled from the case-decl's
   signature and re-emitted as `Param "..."` so they bind the
   witness's references to the actual decl-level params. *)
let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  match s with
  (* 0 constructors: Void *)
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [Void; Absurd (Param mvar, Param scrut)]

  (* 1 constructor: Unit *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      Unit;
      Tt;
      Unit_rec (Param mvar, Param tc, Param scrut);
      Unit_comp (Param mvar2, Param tc2);
    ]

  (* 2 constructors: Bool *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      Bool;
      Yes;
      No;
      Bool_rec (Param mvar, Param tc, Param fc, Param scrut);
      Bool_comp_yes (Param mvar2, Param tc2, Param fc2);
      Bool_comp_no (Param mvar3, Param tc3, Param fc3);
    ]

  | _ -> Error "enum: unsupported number of constructors (expected 0, 1, or 2)"
;;
end

construct by enum
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
end

construct by enum
unit : U
trivial : unit
unit-case (M : U) (trivial-case : M) (scrutinee : unit) : M
unit-case-trivial (M : U) (trivial-case : M) : eq M M (unit-case M trivial-case trivial) trivial-case
end

construct by enum
bool : U
true : bool
false : bool
bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool) : M
bool-case-true (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case true) true-case
bool-case-false (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case false) false-case
end
