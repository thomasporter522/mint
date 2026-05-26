-- enum-nat.mint — ported from main.
-- Approach 6: Nat-indexed enum types. A single generic Enum (n : Nat)
-- family handles arbitrary arities; the schema picks Enum 0 / 1 / 2
-- and produces eliminators via vcons-of-cases + enum-beta-zero /
-- enum-beta-succ proofs.

postulate
U : U
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
end

meta
let n0 = Zero
let n1 = Succ Zero
let n2 = Succ (Succ Zero)

let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  (* 0 constructors *)
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [Enum n0; Enum_absurd (p mvar, p scrut)]

  (* 1 constructor: Enum 1 *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      Enum n1;
      Ezero n0;
      Enum_elim (n1, p mvar,
                 Vcons (p mvar, n0, p tc, Vnil (p mvar)),
                 p scrut);
      Enum_beta_zero (n0, p mvar2, p tc2, Vnil (p mvar2));
    ]

  (* 2 constructors: Enum 2 *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      Enum n2;
      Ezero n1;
      Esucc (n1, Ezero n0);
      Enum_elim (n2, p mvar,
                 Vcons (p mvar, n1, p tc,
                        Vcons (p mvar, n0, p fc, Vnil (p mvar))),
                 p scrut);
      Enum_beta_zero (n1, p mvar2, p tc2,
                      Vcons (p mvar2, n0, p fc2, Vnil (p mvar2)));
      Trans (p mvar3,
             Enum_elim (n2, p mvar3,
                        Vcons (p mvar3, n1, p tc3,
                               Vcons (p mvar3, n0, p fc3, Vnil (p mvar3))),
                        Esucc (n1, Ezero n0)),
             Enum_elim (n1, p mvar3,
                        Vcons (p mvar3, n0, p fc3, Vnil (p mvar3)),
                        Ezero n0),
             p fc3,
             Enum_beta_succ (n1, p mvar3, p tc3,
                             Vcons (p mvar3, n0, p fc3, Vnil (p mvar3)),
                             Ezero n0),
             Enum_beta_zero (n0, p mvar3, p fc3, Vnil (p mvar3)));
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
