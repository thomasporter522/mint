-- Approach 4: Combinatory logic with typed selectors
--
-- Hybrid approach: use untyped CL domain D for computation (K, S, ap),
-- but instead of coerce/embed (which is unsound), use TYPED SELECTORS
-- that extract results from D-computations applied to typed arguments.
--
-- Key insight: the unsoundness of coerce is that D -> A for arbitrary A
-- lets you inhabit any type (since D is inhabited). But a selector like
-- select2 M d m1 m2 : M is safe because it REQUIRES m1:M and m2:M
-- as inputs — it merely SELECTS between existing inhabitants of M,
-- guided by the D-computation d.
--
-- For the 0-case (falsity), we still need a genuinely empty type,
-- since there are no M-inputs to select between. So we postulate
-- Void separately.
--
-- Soundness: The D-selectors are essentially "interpretations" of
-- D-terms as selection functions on typed inputs. This is sound because:
-- (1) selN always returns one of its M-typed inputs (or an opaque term)
-- (2) the beta laws only hold for specific D-terms (K, SK)
-- (3) no D-term can produce an inhabitant of an empty type
-- Validated by any model where D is a set and selN maps D-elements
-- to projection functions on M^N.
--
-- The approach is sound because selN : D -> M -> ... -> M -> M
-- is really a type-indexed family of functions from D to M^N -> M.
-- Even without the beta laws, selN d m1 ... mN : M is well-typed
-- only if all mi : M. No new M-inhabitants are created.
postulate
Sort : Sort
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)
-- Untyped combinatory logic domain
D : U
K : D
S : D
(ap (f : D) (a : D)) : D
(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)
(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))
-- Void: 0-element type (no way to derive this from D)
Void : U
(absurd (M : U) (v : Void)) : M
-- Typed 1-selector: interprets d:D as a unary selector
(sel1 (M : U) (d : D) (m : M)) : M
(sel1-I (M : U) (m : M)) :
  (eq M M (sel1 M (ap (ap S K) K) m) m)
-- Typed 2-selector: interprets d:D as a binary selector
(sel2 (M : U) (d : D) (m1 : M) (m2 : M)) : M
(sel2-K (M : U) (m1 : M) (m2 : M)) :
  (eq M M (sel2 M K m1 m2) m1)
(sel2-SK (M : U) (m1 : M) (m2 : M)) :
  (eq M M (sel2 M (ap S K) m1 m2) m2)
meta
schema enum = fun s => match s with
  -- 0 constructors: map to Void
  | [(type_name, [], U),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar)]
    => (Ok [Void, (absurd mvar scrut_var)])

  -- 1 constructor: unit via D + sel1
  -- unit = D, trivial = I = SKK, unit-case uses sel1
  | [(type_name, [], U),
     (ctor_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)]
    => (Ok [
      D,
      (ap (ap S K) K),
      (sel1 mvar scrut_var tc_var),
      (sel1-I mvar2 tc_var2)
    ])

  -- 2 constructors: bool via D + sel2
  -- bool = D, true = K, false = SK
  | [(type_name, [], U),
     (true_name, [], type_name),
     (false_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _)]
    => (Ok [
      D,
      K,
      (ap S K),
      (sel2 mvar scrut_var tc_var fc_var),
      (sel2-K mvar2 tc2 fc2),
      (sel2-SK mvar3 tc3 fc3)
    ])

  | _ => (Error "enum: unsupported (expected 0, 1, or 2 constructors)")
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
