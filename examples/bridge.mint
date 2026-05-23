// example-bridge.mint — exercises the Mint kernel-bridge module from
// meta code. The schema inspects each signature, asks Mint to make
// some witnesses include holes, and falls back to `Mint.canonical`
// for any signature it can't handle.

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
  | Zero -> "Zero"
  | Suc m -> "Suc(" ^ string_of_term m ^ ")"
  | _ when Mint.is_hole t -> "?"
  | _ when Mint.is_meta t ->
    (match Mint.meta_id t with
     | Some n -> Printf.sprintf "?M%d" n
     | None -> "?M")
  | _ -> "<extension>"
;;

(* A schema that returns Zero for the first decl, a hole for the second,
   and Suc(Suc Zero) for everything else — exercising the bridge's
   Mint.hole () constructor for witnesses that include placeholders. *)
let mixed_schema (_outer : signature list) (sigs : signature list)
    : (term list, string) result =
  Ok (List.mapi (fun i _ ->
    match i with
    | 0 -> Zero
    | 1 -> Mint.hole ()
    | _ -> Suc (Suc Zero)
  ) sigs)
;;
end

construct by mixed_schema
A : Tag
B : Tag
C : Tag
end
