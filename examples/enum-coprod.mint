-- Approach 5: Coproduct-based enums via Arr
--
-- Postulate Void, Unit, binary coproduct (Either), and Arr (function space).
-- Enums as iterated coproducts:
--   falsity = Void
--   unit    = Unit
--   bool    = Either Unit Unit
--
-- For 'either', the case functions are typed using Arr:
--   either : (A:U) -> (B:U) -> (M:U) -> Arr A M -> Arr B M -> Either A B -> M
--
-- We also need lam (to construct case functions) and app + beta
-- (to state the computation rule).
--
-- For the construct blocks, the case witnesses wrap the flat arguments
-- into constant functions via the const combinator.
--
-- Soundness: All postulates are standard categorical constructions
-- (initial/terminal objects, coproducts, function space).
-- Validated by any locally cartesian closed category with finite
-- coproducts. No universal coercion.
--
-- Minimality: Arr + lam + app are needed to type the either cases.
-- This is more postulates than Approach 2, but the decomposition
-- (Void + Unit + Either) is more modular and scales uniformly.
postulate
Sort : Sort
U : Sort
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
meta
schema enum = fun s => match s with
  -- 0 constructors: Void
  | [(type_name, [], U),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar)]
    => (Ok [Void, (absurd mvar scrut_var)])

  -- 1 constructor: Unit
  -- trivial = star
  -- unit-case M tc scrut = unit-rec M tc scrut
  -- unit-case-trivial = unit-comp M tc
  | [(type_name, [], U),
     (ctor_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)]
    => (Ok [
      Unit,
      star,
      (unit-rec mvar tc_var scrut_var),
      (unit-comp mvar2 tc_var2)
    ])

  -- 2 constructors: Either Unit Unit
  -- true = inl Unit Unit star
  -- false = inr Unit Unit star
  -- bool-case M tc fc scrut =
  --   either Unit Unit M (const Unit M tc) (const Unit M fc) scrut
  -- bool-case-true M tc fc :
  --   either(... , inl Unit Unit star)
  --   = app(const Unit M tc, star)     [by either-inl]
  --   = tc                              [by const-beta]
  | [(type_name, [], U),
     (true_name, [], type_name),
     (false_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)]
    => (Ok [
      (Either Unit Unit),
      (inl Unit Unit star),
      (inr Unit Unit star),
      (either Unit Unit mvar (const Unit mvar tc_var) (const Unit mvar fc_var) scrut_var),
      (trans mvar2
        (either Unit Unit mvar2 (const Unit mvar2 tc2) (const Unit mvar2 fc2) (inl Unit Unit star))
        (app Unit mvar2 (const Unit mvar2 tc2) star)
        tc2
        (either-inl Unit Unit mvar2 (const Unit mvar2 tc2) (const Unit mvar2 fc2) star)
        (const-beta Unit mvar2 tc2 star)),
      (trans mvar3
        (either Unit Unit mvar3 (const Unit mvar3 tc3) (const Unit mvar3 fc3) (inr Unit Unit star))
        (app Unit mvar3 (const Unit mvar3 fc3) star)
        fc3
        (either-inr Unit Unit mvar3 (const Unit mvar3 tc3) (const Unit mvar3 fc3) star)
        (const-beta Unit mvar3 fc3 star))
    ])

  | _ => (Error "enum: unsupported (expected 0, 1, or 2 constructors)")
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
end
