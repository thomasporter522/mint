-- incomplete-witness-bad.mint — ported from main.
--
-- The schema returns a witness for `void-rec` whose `cast` is missing
-- its `teq A B` proof (left as a hole). After elaboration the meta
-- introduced for that position has no solution, so the kernel should
-- report an "implicit argument not solved" warning on the witness.
-- This is a NEGATIVE test: it must FAIL to type-check cleanly.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U

to (A : U) (B : U) : U
ap (A : U) (B : U) (f : to A B) (a : A) : B
I (X : U) : to X X
I-eq (X : U) (x : X) : eq (ap I x) x
K (X : U) (A : U) : to A (to X A)
K-eq (X : U) (A : U) (a : A) (x : X) : eq (ap (ap K a) x) a
S (X : U) (A : U) (B : U) : (to (to X (to A B)) (to (to X A) (to X B)))
S-eq (X : U) (A : U) (B : U) (f : to X (to A B)) (a : to X A) (x : X)
    : eq (ap (ap (ap S f) a) x) (ap (ap f x) (ap a x))

teq (A : U) (B : U) : U
to-cong (A1 : U) (A2 : U) (B1 : U) (B2 : U) (e1 : teq A1 A2) (e2 : teq B1 B2) : teq (to A1 B1) (to A2 B2)
cast (A : U) (B : U) (e : teq A B) : to A B
tto : U
tap (f : tto) (X : U) : U

forall (f : tto) : U
forall-elim (F : tto) (X : U) : to (forall F) (tap F X)

tI : tto
tI-tap (X : U) : teq (tap tI X) X
end

meta
(* schema void-schema (main meta): see incomplete-witness-bad on main.
   In OCaml meta the underapplied `cast` cannot be spelled directly —
   OCaml constructors are not curried — so we pass the three implicit
   args as explicit holes. The semantics match: each hole becomes an
   unsolved meta, which the kernel reports. *)
let void_schema (_outer : signature list) (s : signature list)
    : (term list, string) result =
  match s with
  | [_; { params = [(m_name, _)]; _ }] ->
    let m = Param m_name in
    Ok [
      Forall TI;
      Ap (Mint.hole (), Mint.hole (),
          Cast (Mint.hole (), Mint.hole (), Mint.hole ()),
          Forall_elim (TI, m));
    ]
  | _ -> Error "void-schema: expected 2 decls"
;;
end

construct by void_schema
void : U
void-rec (M : U) : to void M
end
