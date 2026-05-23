// example-tagged.mint — exercises tag lines attached to construct-block
// decls. The schema sees each signature's `tags` list and can pick
// witnesses based on it.

postulate
Sort : Sort
Nat : Sort
Zero : Nat
Suc (n : Nat) : Nat
Tag : Sort
end

meta
let rec string_of_term t =
  match t with
  | Sort -> "Sort" | Tag -> "Tag" | Nat -> "Nat"
  | Zero -> "Zero" | Suc m -> "Suc(" ^ string_of_term m ^ ")"
  | _ -> "<ext>"
;;

(* Schema picks Zero or Suc Zero based on a "double" tag. *)
let tagged_schema (_outer : signature list) (sigs : signature list)
    : (term list, string) result =
  Ok (List.map (fun s ->
    if List.mem "double" s.tags then Suc (Suc Zero)
    else Zero
  ) sigs)
;;
end

construct by tagged_schema
Foo : Tag
Bar : Tag
Baz : Tag
#double Bar
end
