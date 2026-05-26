-- enum-tarski.mint — ported from main.
--
-- Tarski-style universe with codes: postulate Code : Sort and
-- El : Code -> U, plus specific enum codes (void-c, unit-c, bool-c)
-- with their decoders and beta rules. The schema maps each construct
-- shape to the corresponding El c.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
Code : U
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
end

meta
let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [El Void_c; Void_elim (p mvar, p scrut)]

  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      El Unit_c;
      Unit_val;
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
      El Bool_c;
      Yes_val;
      No_val;
      Bool_elim (p mvar, p tc, p fc, p scrut);
      Bool_yes_beta (p mvar2, p tc2, p fc2);
      Bool_no_beta (p mvar3, p tc3, p fc3);
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
