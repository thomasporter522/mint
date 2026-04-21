-- Church-encoded enums via untyped combinatory logic (Approach A)
--
-- Postulates: combinatory logic domain D with K/S/ap,
-- coerce/embed retraction between D and any type in U,
-- plus standard congruence lemmas.
--
-- Key idea: enum types are witnessed by D.
-- Constructors are Church selectors (K for 1st, SK for 2nd, I=SKK for sole).
-- Case elimination applies the embedded scrutinee to embedded branches.
-- Equations proved by SK-reduction + retraction.
postulate
Sort : Sort
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)
D : U
K : D
S : D
(ap (f : D) (a : D)) : D
(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)
(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))
(coerce (A : U) (d : D)) : A
(embed (A : U) (a : A)) : D
(retract (A : U) (a : A)) : (eq A A (coerce A (embed A a)) a)
(embed-D (x : D)) : (eq D D (embed D x) x)
(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))
(coerce-cong (A : U) (x : D) (y : D) (e : (eq D D x y))) : (eq A A (coerce A x) (coerce A y))
meta
-- Proof helpers: reusable SK-reduction lemmas
-- K-selector: ap(ap(embed D K) x) y = x
k-select-proof = fun x => fun y =>
  (trans D
    (ap (ap (embed D K) x) y)
    (ap (ap K x) y)
    x
    (ap-cong (ap (embed D K) x) (ap K x) y
      (ap-cong (embed D K) K x (embed-D K)))
    (ap-K x y))

-- SK-selector: ap(ap(embed D (ap S K)) x) y = y
sk-select-proof = fun x => fun y =>
  (trans D
    (ap (ap (embed D (ap S K)) x) y)
    (ap (ap (ap S K) x) y)
    y
    (ap-cong (ap (embed D (ap S K)) x) (ap (ap S K) x) y
      (ap-cong (embed D (ap S K)) (ap S K) x (embed-D (ap S K))))
    (trans D
      (ap (ap (ap S K) x) y)
      (ap (ap K y) (ap x y))
      y
      (ap-S K x y)
      (ap-K y (ap x y))))

-- I-selector: ap(embed D (ap(ap S K)K)) x = x
i-select-proof = fun x =>
  (trans D
    (ap (embed D (ap (ap S K) K)) x)
    (ap (ap (ap S K) K) x)
    x
    (ap-cong (embed D (ap (ap S K) K)) (ap (ap S K) K) x (embed-D (ap (ap S K) K)))
    (trans D
      (ap (ap (ap S K) K) x)
      (ap (ap K x) (ap K x))
      x
      (ap-S K K x)
      (ap-K x (ap K x))))

-- Generic enum schema: dispatches on number of constructors
schema enum = fun s => match s with
  -- 0 constructors (falsity): type = D, case = coerce
  | [(type_name, [], U),
     (case_name, [(mvar, U), (scrut_var, type_name)], mvar)]
    => (Ok [D, (coerce mvar scrut_var)])

  -- 1 constructor (unit): ctor = I, case = coerce(ap(embed scrutinee)(embed arg))
  | [(type_name, [], U),
     (ctor_name, [], type_name),
     (case_name, [(mvar, U), (tc_var, mvar), (scrut_var, type_name)], mvar),
     (eq_name, [(mvar2, U), (tc_var2, mvar2)], _)]
    => (Ok [
      D,
      (ap (ap S K) K),
      (coerce mvar (ap (embed D scrut_var) (embed mvar tc_var))),
      (trans mvar
        (coerce mvar (ap (embed D (ap (ap S K) K)) (embed mvar2 tc_var2)))
        (coerce mvar (embed mvar2 tc_var2))
        tc_var2
        (coerce-cong mvar
          (ap (embed D (ap (ap S K) K)) (embed mvar2 tc_var2))
          (embed mvar2 tc_var2)
          (i-select-proof (embed mvar2 tc_var2)))
        (retract mvar2 tc_var2))
    ])

  -- 2 constructors (bool): true = K, false = SK
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
      (coerce mvar (ap (ap (embed D scrut_var) (embed mvar tc_var)) (embed mvar fc_var))),
      (trans mvar2
        (coerce mvar2 (ap (ap (embed D K) (embed mvar2 tc2)) (embed mvar2 fc2)))
        (coerce mvar2 (embed mvar2 tc2))
        tc2
        (coerce-cong mvar2
          (ap (ap (embed D K) (embed mvar2 tc2)) (embed mvar2 fc2))
          (embed mvar2 tc2)
          (k-select-proof (embed mvar2 tc2) (embed mvar2 fc2)))
        (retract mvar2 tc2)),
      (trans mvar3
        (coerce mvar3 (ap (ap (embed D (ap S K)) (embed mvar3 tc3)) (embed mvar3 fc3)))
        (coerce mvar3 (embed mvar3 fc3))
        fc3
        (coerce-cong mvar3
          (ap (ap (embed D (ap S K)) (embed mvar3 tc3)) (embed mvar3 fc3))
          (embed mvar3 fc3)
          (sk-select-proof (embed mvar3 tc3) (embed mvar3 fc3)))
        (retract mvar3 fc3))
    ])

  | _ => (Error "enum schema: unsupported number of constructors (expected 0, 1, or 2)")
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
