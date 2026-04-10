-- Generic coproduct-based enums
-- Attempt to make the enum schema handle arbitrary N constructors
postulate
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)
(Arr (A : U) (B : U)) : U
(app (A : U) (B : U) (f : (Arr A B)) (a : A)) : B
(const (A : U) (B : U) (b : B)) : (Arr A B)
(const-beta (A : U) (B : U) (b : B) (a : A)) :
  (eq B B (app A B (const A B b) a) b)
Void : U
(absurd (M : U) (v : Void)) : M
Unit : U
star : Unit
(unit-rec (M : U) (star-case : M) (u : Unit)) : M
(unit-comp (M : U) (star-case : M)) :
  (eq M M (unit-rec M star-case star) star-case)
(Either (A : U) (B : U)) : U
(inl (A : U) (B : U) (a : A)) : (Either A B)
(inr (A : U) (B : U) (b : B)) : (Either A B)
(either (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (e : (Either A B))) : M
(either-inl (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (a : A)) :
  (eq M M (either A B M f g (inl A B a)) (app A M f a))
(either-inr (A : U) (B : U) (M : U) (f : (Arr A M)) (g : (Arr B M)) (b : B)) :
  (eq M M (either A B M f g (inr A B b)) (app B M g b))
(app-cong (A : U) (B : U) (f : (Arr A B)) (g : (Arr A B)) (x : A) (e : (eq (Arr A B) (Arr A B) f g))) : (eq B B (app A B f x) (app A B g x))
meta
-- Build the iterated coproduct type for N constructors:
-- 0 ctors -> Void
-- 1 ctor  -> Unit
-- 2 ctors -> Either Unit Unit
-- 3 ctors -> Either Unit (Either Unit Unit)
-- Pattern: Either Unit (Either Unit (... Unit))
--
-- To build right-nested, I need to fold from the RIGHT.
-- foldl builds left-nested. I need foldr or reverse.
--
-- Missing: foldr, reverse, length, nth
--
-- Let me try with what I have...
-- Actually, foldl (fun acc => fun _ => (Either Unit acc)) Unit [c1, c2]
-- gives: start=Unit, after c1: Either Unit Unit, after c2: Either Unit (Either Unit Unit)
-- Wait — that IS right-nested from the perspective of adding on the left!
-- For 1 ctor:  Unit (no fold needed)
-- For 2 ctors: foldl over [c2] starting from Unit → Either Unit Unit ✓
-- For 3 ctors: foldl over [c2, c3] starting from Unit → Either Unit (Either Unit Unit) ✓
-- The trick: drop the first constructor, fold the REST, wrapping with Either Unit on each step.
-- The first constructor uses Unit as its slot.

-- But I also need to build:
-- Constructor i's injection term (inl/inr chain)
-- The case eliminator
-- The equation proofs
-- All of which depend on the nesting depth.

-- For constructor terms:
-- c0 (first): inl Unit <rest> star  (when N >= 2)
--             star                   (when N == 1)
-- c1 (second): inr Unit <rest> (inl Unit <rest'> star)  (when N >= 3)
--              inr Unit Unit star                        (when N == 2)
-- ci: wrap in i layers of inr, then one inl, then star

-- For the case eliminator with N ctors and M motive:
-- either A B M (const A M tc0) (either-based-rec for rest) scrut
-- This is also recursive.

-- I think I need: reverse, map, and some way to build nested terms.
-- Let me see what I can do...

-- For now, let me just test: can I build the TYPE generically?
schema enum = fun s => match s with
  -- 0 constructors: Void
  | [(type_name, [], U),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar)]
    => (Ok [Void, (absurd mvar scrut_var)])

  -- Generic N >= 1: try to handle uniformly
  | _ => (Error "TODO: generic case not implemented")
  end
construct by enum
  falsity : U
  (falsity-case (M : U) (scrutinee : falsity)) : M
end
