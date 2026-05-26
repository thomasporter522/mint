-- simple.mint — ported from main.
--
-- Encodes void and unit via a Church-style "forall F" universe.
-- void-schema gives the witness for `void` and `void-rec`.
-- unit-schema gives the witness for `unit`, `star`, `unit-rec`, and the
-- beta-equation `unit-iota`. Two of unit-schema's witnesses are
-- intentionally `?` (incomplete proofs of the missing teq /
-- eq-direction) so the suite expects "unsolved meta" warnings.
--
-- Known gap vs. main: unit-rec's witness type-checks only modulo
-- `tabs-to-tap` and `tI-tap` (postulate equations the kernel does
-- not auto-rewrite). Without a coercion-search procedure wired into
-- the slice, the kernel reports "Type mismatch on forall-elim". That
-- mirrors main's behavior pre-coerce-beta.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a

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
trefl (A : U) : teq A A
to-cong (A1 : U) (A2 : U) (B1 : U) (B2 : U) (e1 : teq A1 A2) (e2 : teq B1 B2) : teq (to A1 B1) (to A2 B2)
cast (A : U) (B : U) (e : teq A B) : to A B
tto : U
tap (f : tto) (X : U) : U

forall (f : tto) : U
forall-elim (F : tto) (X : U) : to (forall F) (tap F X)

tI : tto
tI-tap (X : U) : teq (tap tI X) X

tabs-to (A : tto) (B : tto) : tto
tabs-to-tap (A : tto) (B : tto) (X : U) : teq (tap (tabs-to A B) X) (to (tap A X) (tap B X))
end

meta
(* schema void-schema (main meta): see simple.mint on main.
   We pass leading implicits as explicit Mint.hole () because OCaml
   constructors aren't curried — `cast`, `to-cong`, `trefl`,
   `tI-tap`, `forall-elim`, `ap` all have leading implicit args that
   the elaborator solves from the surrounding type. *)
let void_schema (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let h = Mint.hole in
  match s with
  | [_; { params = [(m_name, _)]; _ }] ->
    let m = Param m_name in
    Ok [
      Forall TI;
      Ap (h (), h (),
          Cast (h (), h (),
                To_cong (h (), h (), h (), h (),
                         Trefl (h ()),
                         TI_tap (h ()))),
          Forall_elim (TI, m));
    ]
  | _ -> Error "void-schema: expected 2 decls"
;;
end

construct by void_schema
void : U
void-rec (M : U) : to void M
end

meta
(* schema unit-schema (main meta): see simple.mint on main.
   Two witnesses are intentionally `?` — they would need the
   teq-direction proof for unit, which simple.mint leaves out.
   Expected output: "Witness contains unsolved metavariables" on
   star and unit-iota. *)
let unit_schema (_outer : signature list) (s : signature list)
    : (term list, string) result =
  let h = Mint.hole in
  match s with
  | [_; _; { params = [(m_name, _)]; _ }; _] ->
    let m = Param m_name in
    Ok [
      Forall (Tabs_to (TI, TI));
      h ();
      Forall_elim (Tabs_to (TI, TI), m);
      h ();
    ]
  | _ -> Error "unit-schema: expected 4 decls"
;;
end

construct by unit_schema
unit : U
star : unit
unit-rec (M : U) : to unit (to M M)
unit-iota (M : U) (star-case : M) : eq (ap (ap (unit-rec M) star) star-case) star-case
end
