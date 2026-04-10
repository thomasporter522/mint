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
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)
-- Function space (for typing case functions in either)
(Arr (A : U) (B : U)) : U
(app (A : U) (B : U) (f : (Arr A B)) (a : A)) : B
-- Constant function combinator: const A B b is \_ : A. b
(const (A : U) (B : U) (b : B)) : (Arr A B)
(const-beta (A : U) (B : U) (b : B) (a : A)) :
  (eq B B (app A B (const A B b) a) b)
-- Void: initial object (0-element type)
Void : U
(absurd (M : U) (v : Void)) : M
-- Unit: terminal object (1-element type)
Unit : U
star : Unit
(unit-rec (M : U) (star-case : M) (u : Unit)) : M
(unit-comp (M : U) (star-case : M)) :
  (eq M M (unit-rec M star-case star) star-case)
-- Either: binary coproduct
(Either (A : U) (B : U)) : U
(inl (A : U) (B : U) (a : A)) : (Either A B)
(inr (A : U) (B : U) (b : B)) : (Either A B)
(either (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (e : (Either A B))) : M
(either-inl (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (a : A)) :
  (eq M M (either A B M f g (inl A B a)) (app A M f a))
(either-inr (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (b : B)) :
  (eq M M (either A B M f g (inr A B b)) (app B M g b))
-- Congruence for app (needed for eq chains)
(app-cong (A : U) (B : U) (f : (Arr A B)) (g : (Arr A B)) (x : A) (e : (eq (Arr A B) (Arr A B) f g))) : (eq B B (app A B f x) (app A B g x))
meta
schema enum = fun s => 
  ? -- TODO: operate generically over any number of constructors. The four below are good tests.  
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
construct by enum
  color : U
  red : color
  yellow : color
  green : color
  blue : color
  -- TODO
end
