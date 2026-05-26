-- enum-coprod.mint — ported from main.
--
-- 0/1/2-element enums as iterated coproducts of Unit:
--   falsity = Void
--   unit    = Unit
--   bool    = Either Unit Unit
-- Case witnesses use lam/app/either-beta + const-beta for the
-- elimination + computation proofs.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Arr (A : U) (B : U) : U
app (A : U) (B : U) (f : Arr A B) (a : A) : B
const (A : U) (B : U) (b : B) : Arr A B
const-beta (A : U) (B : U) (b : B) (a : A) : eq B B (app A B (const A B b) a) b
Void : U
absurd (M : U) (v : Void) : M
Unit : U
star : Unit
unit-rec (M : U) (star-case : M) (u : Unit) : M
unit-comp (M : U) (star-case : M) : eq M M (unit-rec M star-case star) star-case
Either (A : U) (B : U) : U
inl (A : U) (B : U) (a : A) : Either A B
inr (A : U) (B : U) (b : B) : Either A B
either (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (e : Either A B) : M
either-inl (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (a : A) : eq M M (either A B M f g (inl A B a)) (app A M f a)
either-inr (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (b : B) : eq M M (either A B M f g (inr A B b)) (app B M g b)
app-cong (A : U) (B : U) (f : Arr A B) (g : Arr A B) (x : A) (e : eq (Arr A B) (Arr A B) f g) : eq B B (app A B f x) (app A B g x)
end

meta
let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  (* 0 constructors: Void *)
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [Void; Absurd (p mvar, p scrut)]

  (* 1 constructor: Unit *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      Unit;
      Star;
      Unit_rec (p mvar, p tc, p scrut);
      Unit_comp (p mvar2, p tc2);
    ]

  (* 2 constructors: Either Unit Unit *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      Either (Unit, Unit);
      Inl (Unit, Unit, Star);
      Inr (Unit, Unit, Star);
      Either_2 (Unit, Unit, p mvar,
               Const (Unit, p mvar, p tc),
               Const (Unit, p mvar, p fc),
               p scrut);
      Trans (p mvar2,
             Either_2 (Unit, Unit, p mvar2,
                      Const (Unit, p mvar2, p tc2),
                      Const (Unit, p mvar2, p fc2),
                      Inl (Unit, Unit, Star)),
             App (Unit, p mvar2,
                  Const (Unit, p mvar2, p tc2),
                  Star),
             p tc2,
             Either_inl (Unit, Unit, p mvar2,
                         Const (Unit, p mvar2, p tc2),
                         Const (Unit, p mvar2, p fc2),
                         Star),
             Const_beta (Unit, p mvar2, p tc2, Star));
      Trans (p mvar3,
             Either_2 (Unit, Unit, p mvar3,
                      Const (Unit, p mvar3, p tc3),
                      Const (Unit, p mvar3, p fc3),
                      Inr (Unit, Unit, Star)),
             App (Unit, p mvar3,
                  Const (Unit, p mvar3, p fc3),
                  Star),
             p fc3,
             Either_inr (Unit, Unit, p mvar3,
                         Const (Unit, p mvar3, p tc3),
                         Const (Unit, p mvar3, p fc3),
                         Star),
             Const_beta (Unit, p mvar3, p fc3, Star));
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
