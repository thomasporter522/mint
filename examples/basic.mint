// example.mint — postulate / meta / construct exercising arg-bearing
// decls and a user-defined universe atom. The kernel has zero built-in
// term-formers; the user declares everything, including the self-typed
// bootstrap (here called `Sort`, but any name would do).
//
// Run via:  ./main.bc.exe example.mint

postulate
Sort : Sort
Nat : Sort
Zero : Nat
Suc (n : Nat) : Nat
Tag : Sort
end

meta
(* string_of_term covers the constructors that exist at definition time
   plus a catch-all for whatever the construct block adds below. *)
let rec string_of_term t =
  match t with
  | Sort -> "Sort"
  | Tag -> "Tag"
  | Nat -> "Nat"
  | Zero -> "Zero"
  | Suc m -> "Suc(" ^ string_of_term m ^ ")"
  | _ -> "<extension>"
;;

(* A schema: given a list of declared signatures, return Suc^i Zero
   for the i-th decl. The kernel verifies each witness against the
   decl's declared return type — so this schema is well-formed only
   when invoked on a construct block whose decls all expect Nat. *)
let enum_schema (_outer : signature list) (sigs : signature list)
    : (term list, string) result =
  let rec build n =
    if n = 0 then Zero
    else Suc (build (n - 1))
  in
  Ok (List.mapi (fun i _ -> build i) sigs)
;;
end

construct by enum_schema
Foo : Nat
Bar : Nat
Baz : Nat
end
