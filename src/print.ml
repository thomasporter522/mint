(* OL pretty-printing. Shared between mintc's source-summary and the
   kernel's inlay-hint extractor (which needs to render the inferred
   value of each implicit argument as a tooltip). *)

open Ast

let rec print_ol (t : ol) : string =
  let pchild (s : ol) =
    match s.value with
    | OLAp (_, _ :: _) when not s.meta.parens ->
      "(" ^ print_ol s ^ ")"
    | _ -> print_ol s
  in
  let inner = match t.value with
    | OLHole -> "?"
    | OLMeta _ -> "?"
    | OLAp (f, []) -> f.string
    | OLAp (f, args) ->
      f.string ^ " " ^ String.concat " " (List.map pchild args)
  in
  if t.meta.parens then "(" ^ inner ^ ")" else inner
