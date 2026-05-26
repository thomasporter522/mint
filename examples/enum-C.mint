-- enum-C.mint — ported from main.
-- Approach C: codes (falsity-code / unit-code / bool-code) and an
-- El decoder; the schema maps each construct shape to the
-- corresponding El c.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
Code : U
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
end

meta
let enum_from_codes (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [El Falsity_code; Falsity_elim (p mvar, p scrut)]

  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      El Unit_code;
      Triv;
      Unit_elim (p mvar, p tc, p scrut);
      Unit_beta (p mvar2, p tc2);
    ]

  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      El Bool_code;
      Tt;
      Ff;
      Bool_elim (p mvar, p tc, p fc, p scrut);
      Bool_beta_tt (p mvar2, p tc2, p fc2);
      Bool_beta_ff (p mvar3, p tc3, p fc3);
    ]

  | _ -> Error "unknown enum shape"
;;
end

construct by enum_from_codes
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
end

construct by enum_from_codes
unit : U
trivial : unit
unit-case (M : U) (trivial-case : M) (scrutinee : unit) : M
unit-case-trivial (M : U) (trivial-case : M) : eq M M (unit-case M trivial-case trivial) trivial-case
end

construct by enum_from_codes
bool : U
true : bool
false : bool
bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool) : M
bool-case-true (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case true) true-case
bool-case-false (M : U) (true-case : M) (false-case : M) : eq M M (bool-case M true-case false-case false) false-case
end
