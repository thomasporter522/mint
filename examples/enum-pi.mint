-- enum-pi.mint — ported from main.
--
-- Encodes 0/1/2-element enums via impredicative ForallArrN types
-- with specific inhabitants (polyId, polyK, polyFlipK) and their
-- inst+beta laws. The schema produces eliminators + computation
-- proofs entirely from postulate equations — no coercion needed.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Arr (A : U) (B : U) : U
app (A : U) (B : U) (f : Arr A B) (a : A) : B
K (A : U) (B : U) : Arr A (Arr B A)
K-beta (A : U) (B : U) (x : A) (y : B) : eq A A (app B A (app A (Arr B A) (K A B) x) y) x
flip-K (A : U) (B : U) : Arr A (Arr B B)
flip-K-beta (A : U) (B : U) (x : A) (y : B) : eq B B (app B B (app A (Arr B B) (flip-K A B) x) y) y
I (A : U) : Arr A A
I-beta (A : U) (x : A) : eq A A (app A A (I A) x) x
app-cong (A : U) (B : U) (f : Arr A B) (g : Arr A B) (x : A) (e : eq (Arr A B) (Arr A B) f g) : eq B B (app A B f x) (app A B g x)
ForallArr0 : U
inst0 (M : U) (f : ForallArr0) : M
ForallArr1 : U
inst1 (M : U) (f : ForallArr1) : Arr M M
polyId : ForallArr1
polyId-beta (M : U) : eq (Arr M M) (Arr M M) (inst1 M polyId) (I M)
ForallArr2 : U
inst2 (M : U) (f : ForallArr2) : Arr M (Arr M M)
polyK : ForallArr2
polyK-beta (M : U) : eq (Arr M (Arr M M)) (Arr M (Arr M M)) (inst2 M polyK) (K M M)
polyFlipK : ForallArr2
polyFlipK-beta (M : U) : eq (Arr M (Arr M M)) (Arr M (Arr M M)) (inst2 M polyFlipK) (flip-K M M)
end

meta
(* schema enum (main meta): pattern-match by signature shape and
   emit the System-F-encoded witness. Each constructor reference
   becomes the corresponding OCaml constructor; pattern variables
   are emitted as `Param "..."` so the kernel binds them to the
   case-decl's actual params. *)
let enum (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let p = Mint.param in
  match s with
  (* 0 constructors: falsity *)
  | [{ params = []; _ };
     { params = [(mvar, _); (scrut, _)]; _ }] ->
    Ok [ForallArr0; Inst0 (p mvar, p scrut)]

  (* 1 constructor: unit *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _)]; _ }] ->
    Ok [
      ForallArr1;
      PolyId;
      App (p mvar, p mvar, Inst1 (p mvar, p scrut), p tc);
      Trans (p mvar2,
             App (p mvar2, p mvar2, Inst1 (p mvar2, PolyId), p tc2),
             App (p mvar2, p mvar2, I (p mvar2), p tc2),
             p tc2,
             App_cong (p mvar2, p mvar2,
                       Inst1 (p mvar2, PolyId), I (p mvar2),
                       p tc2,
                       PolyId_beta (p mvar2)),
             I_beta (p mvar2, p tc2));
    ]

  (* 2 constructors: bool *)
  | [{ params = []; _ };
     { params = []; _ };
     { params = []; _ };
     { params = [(mvar, _); (tc, _); (fc, _); (scrut, _)]; _ };
     { params = [(mvar2, _); (tc2, _); (fc2, _)]; _ };
     { params = [(mvar3, _); (tc3, _); (fc3, _)]; _ }] ->
    Ok [
      ForallArr2;
      PolyK;
      PolyFlipK;
      App (p mvar, p mvar,
           App (p mvar, Arr (p mvar, p mvar),
                Inst2 (p mvar, p scrut),
                p tc),
           p fc);
      Trans (p mvar2,
             App (p mvar2, p mvar2,
                  App (p mvar2, Arr (p mvar2, p mvar2),
                       Inst2 (p mvar2, PolyK), p tc2),
                  p fc2),
             App (p mvar2, p mvar2,
                  App (p mvar2, Arr (p mvar2, p mvar2),
                       K (p mvar2, p mvar2), p tc2),
                  p fc2),
             p tc2,
             App_cong (p mvar2, p mvar2,
                       App (p mvar2, Arr (p mvar2, p mvar2),
                            Inst2 (p mvar2, PolyK), p tc2),
                       App (p mvar2, Arr (p mvar2, p mvar2),
                            K (p mvar2, p mvar2), p tc2),
                       p fc2,
                       App_cong (p mvar2, Arr (p mvar2, p mvar2),
                                 Inst2 (p mvar2, PolyK),
                                 K (p mvar2, p mvar2),
                                 p tc2,
                                 PolyK_beta (p mvar2))),
             K_beta (p mvar2, p mvar2, p tc2, p fc2));
      Trans (p mvar3,
             App (p mvar3, p mvar3,
                  App (p mvar3, Arr (p mvar3, p mvar3),
                       Inst2 (p mvar3, PolyFlipK), p tc3),
                  p fc3),
             App (p mvar3, p mvar3,
                  App (p mvar3, Arr (p mvar3, p mvar3),
                       Flip_K (p mvar3, p mvar3), p tc3),
                  p fc3),
             p fc3,
             App_cong (p mvar3, p mvar3,
                       App (p mvar3, Arr (p mvar3, p mvar3),
                            Inst2 (p mvar3, PolyFlipK), p tc3),
                       App (p mvar3, Arr (p mvar3, p mvar3),
                            Flip_K (p mvar3, p mvar3), p tc3),
                       p fc3,
                       App_cong (p mvar3, Arr (p mvar3, p mvar3),
                                 Inst2 (p mvar3, PolyFlipK),
                                 Flip_K (p mvar3, p mvar3),
                                 p tc3,
                                 PolyFlipK_beta (p mvar3))),
             Flip_K_beta (p mvar3, p mvar3, p tc3, p fc3));
    ]

  | _ -> Error "enum: unsupported number of constructors"
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
