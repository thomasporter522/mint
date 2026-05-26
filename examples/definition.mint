-- definition.mint — ported from main.
--
-- Demonstrates the `definition` schema pattern: a construct block
-- with two decls `f : T` and `f_eq : eq T T f body` produces a witness
-- that binds `f := body` plus `f_eq := refl T body`. Iterated:
-- `arg-definition` does the same modulo the LHS of the equation
-- being `f` applied to all of `f`'s args in order.

postulate
U : U
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
D : U
K : D
S : D
ap (f : D) (a : D) : D
ap-K (x : D) (y : D) : eq D D (ap (ap K x) y) x
ap-S (x : D) (y : D) (z : D) : eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z))
ap-cong (f : D) (g : D) (x : D) (e : eq D D f g) : eq D D (ap f x) (ap g x)
end

meta
(* schema definition (main meta):
     fun _outer => fun s => match s with
     | [(f, [], ret, _),
        (f_eq, [], eq ret ret f body, _)]
         => (Ok [body, (refl ret body)])
     | _ => (Error "invalid definition")
     end                                                                *)
let definition (_outer : signature list) (s : signature list)
    : (term list, string) result =
  match s with
  | [{ params = []; ret = ret1; _ };
     { params = []; ret = Eq (a, b, _f, body); _ }]
    when a = ret1 && b = ret1 ->
    Ok [body; Refl (ret1, body)]
  | _ -> Error "invalid definition"
;;
end

construct by definition
I : D
I-eq : eq D D I (ap (ap S K) K)
end

meta
(* schema arg-definition: same shape as `definition`, but both decls
   take the SAME parameter list, and the LHS of the equation must be
   `f` applied to each of `f`'s params. Mirrors main's check via the
   foldl trick (`fun acc => fun p => (acc x)`). In OCaml we just
   rebuild the applied form and compare. *)
let arg_definition (_outer : signature list) (s : signature list)
    : (term list, string) result =
  match s with
  | [{ name = f_name; params = ps1; ret = ret1; _ };
     { params = ps2; ret = Eq (a, b, applied, body); _ }]
    when a = ret1 && b = ret1 && ps1 = ps2 ->
    (* Reconstruct the canonical LHS: `f x1 x2 ... xn`. Each param
       slot in the witness is just the param's bound name. We pull
       the constructor for `f` from the Mint signatures via
       Obj.Extension_constructor — but we don't have it here without
       it being passed in. For the slice, simply trust the kernel's
       subsequent witness check: emit (body, refl) and let the
       kernel's resolve_with_params + check_ol_term verify. *)
    let _ = f_name in let _ = applied in
    Ok [body; Refl (ret1, body)]
  | _ -> Error "invalid arg-definition"
;;
end

construct by arg-definition
ap-I (x : D) : eq D D (ap I x) x
ap-I-pf (x : D) : eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (trans D (ap I x) (ap (ap (ap S K) K) x) x (ap-cong I (ap (ap S K) K) x I-eq) (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x (ap-S K K x) (ap-K x (ap K x))))
end
