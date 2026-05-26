-- enum-clsel.mint — ported from main.
-- Approach 4: combinatory logic with typed selectors. unit and bool
-- are witnessed by the same domain D but their case eliminators are
-- selN with M-typed inputs, so no unsound coercion is needed.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
D : U
K : D
S : D
ap (f : D) (a : D) : D
ap-K (x : D) (y : D) : eq D D (ap (ap K x) y) x
ap-S (x : D) (y : D) (z : D) : eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z))
Void : U
absurd (M : U) (v : Void) : M
sel1 (M : U) (d : D) (m : M) : M
sel1-I (M : U) (m : M) : eq M M (sel1 M (ap (ap S K) K) m) m
sel2 (M : U) (d : D) (m1 : M) (m2 : M) : M
sel2-K (M : U) (m1 : M) (m2 : M) : eq M M (sel2 M K m1 m2) m1
sel2-SK (M : U) (m1 : M) (m2 : M) : eq M M (sel2 M (ap S K) m1 m2) m2
end

meta
let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [Void; Absurd (p mvar, p scrut)]

  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      D;
      Ap (Ap (S, K), K);
      Sel1 (p mvar, p scrut, p tc);
      Sel1_I (p mvar2, p tc2);
    ]

  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      D;
      K;
      Ap (S, K);
      Sel2 (p mvar, p scrut, p tc, p fc);
      Sel2_K (p mvar2, p tc2, p fc2);
      Sel2_SK (p mvar3, p tc3, p fc3);
    ]

  | _ -> Error "enum: unsupported (expected 0, 1, or 2 constructors)"
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
