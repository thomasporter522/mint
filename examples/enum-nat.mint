-- Approach 6: Natural number-indexed enum types
--
-- Postulate natural numbers (Nat with zero/succ), vectors (Vec : U -> Nat -> U),
-- and a single generic enum type family indexed by Nat:
--   (Enum (n : Nat)) : U
--   (inject (n : Nat) (i : Nat)) : (Enum n)   [i < n]
--   (enum-elim (n : Nat) (M : U) (cases : (Vec M n)) (e : (Enum n))) : M
--   plus beta laws.
--
-- This gives a single generic mechanism for all finite enum types.
--
-- Soundness: The Enum/inject/elim postulates are standard finite type theory.
-- Nat and Vec are standard inductive types. All postulates are validated
-- by the standard set-theoretic model.
--
-- Minimality: The Nat/Vec/Enum hierarchy is more machinery than Approach 2,
-- but it's GENERIC — it handles any arity without new postulates.
postulate
Sort : Sort
U : Sort
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
meta
-- Helper: build 0, 1, 2 as Nat
n0 = zero
n1 = (succ zero)
n2 = (succ (succ zero))

schema enum = fun outer => fun s => match s with
  -- 0 constructors: Enum 0 (empty)
  | [(type_name, [], U, _),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar, _)]
    => (Ok [(Enum n0), (enum-absurd mvar scrut_var)])

  -- 1 constructor: Enum 1
  -- trivial = ezero 0 : Enum 1
  -- unit-case M tc scrut = enum-elim 1 M (vcons M 0 tc (vnil M)) scrut
  -- unit-case-trivial: enum-elim(1, M, vcons(tc, vnil), ezero 0) = tc
  --   by enum-beta-zero
  | [(type_name, [], U, _),
     (ctor_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _, _)]
    => (Ok [
      (Enum n1),
      (ezero n0),
      (enum-elim n1 mvar (vcons mvar n0 tc_var (vnil mvar)) scrut_var),
      (enum-beta-zero n0 mvar2 tc_var2 (vnil mvar2))
    ])

  -- 2 constructors: Enum 2
  -- true = ezero 1 : Enum 2          (index 0 = first constructor)
  -- false = esucc 1 (ezero 0) : Enum 2  (index 1 = second constructor)
  -- bool-case M tc fc scrut =
  --   enum-elim 2 M (vcons M 1 tc (vcons M 0 fc (vnil M))) scrut
  -- bool-case-true:
  --   enum-elim(2, M, vcons(tc, vcons(fc, vnil)), ezero 1)
  --   = tc  [by enum-beta-zero]
  -- bool-case-false:
  --   enum-elim(2, M, vcons(tc, vcons(fc, vnil)), esucc 1 (ezero 0))
  --   = enum-elim(1, M, vcons(fc, vnil), ezero 0)  [by enum-beta-succ]
  --   = fc  [by enum-beta-zero]
  | [(type_name, [], U, _),
     (true_name, [], type_name, _),
     (false_name, [], type_name, _),
     (case_name, [(mvar, U), (tc_var, mvar), (fc_var, mvar), (scrut_var, type_name)], mvar, _),
     (eq_true, [(mvar2, U), (tc2, mvar2), (fc2, mvar2)], _, _),
     (eq_false, [(mvar3, U), (tc3, mvar3), (fc3, mvar3)], _, _)]
    => (Ok [
      (Enum n2),
      (ezero n1),
      (esucc n1 (ezero n0)),
      (enum-elim n2 mvar (vcons mvar n1 tc_var (vcons mvar n0 fc_var (vnil mvar))) scrut_var),
      (enum-beta-zero n1 mvar2 tc2 (vcons mvar2 n0 fc2 (vnil mvar2))),
      (trans mvar3
        (enum-elim n2 mvar3 (vcons mvar3 n1 tc3 (vcons mvar3 n0 fc3 (vnil mvar3))) (esucc n1 (ezero n0)))
        (enum-elim n1 mvar3 (vcons mvar3 n0 fc3 (vnil mvar3)) (ezero n0))
        fc3
        (enum-beta-succ n1 mvar3 tc3 (vcons mvar3 n0 fc3 (vnil mvar3)) (ezero n0))
        (enum-beta-zero n0 mvar3 fc3 (vnil mvar3)))
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
