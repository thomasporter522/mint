(* Diagnostic primitive. Mirrors `reason/src/Error.re` exactly so the
   slice can grow into a drop-in replacement for the Melange kernel's
   error surface. *)

type t = {
  type_: string;     (* "mark" for errors, "warning" for non-fatal *)
  message: string;
  from: int;
  to_: int;
}

let mark message from to_ = { type_ = "mark"; message; from; to_ }
let warn message from to_ = { type_ = "warning"; message; from; to_ }

let is_real (e : t) : bool = e.type_ <> "warning"
let has_real (errs : t list) : bool = List.exists is_real errs

(* Pretty-print a diagnostic with file:line:col, given the source string
   to compute the line and column from the byte offset. *)
let line_col (src : string) (offset : int) : int * int =
  let line = ref 1 in
  let col = ref 1 in
  let i = ref 0 in
  while !i < offset && !i < String.length src do
    if src.[!i] = '\n' then begin
      incr line;
      col := 1
    end else
      incr col;
    incr i
  done;
  (!line, !col)

let pp (path : string) (src : string) (e : t) : string =
  let (line, col) = line_col src e.from in
  let kind = if e.type_ = "warning" then "warning" else "error" in
  Printf.sprintf "%s:%d:%d: %s: %s" path line col kind e.message
