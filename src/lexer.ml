(* Token stream for a single Mint source line. The lexer is line-local —
   block boundaries (postulate / meta / construct / end) are detected in
   `parser.ml` before lex runs. Identifiers allow hyphens to match
   Mint's surface convention. *)

type token =
  | TIdent of string
  | TLParen
  | TRParen
  | TColon
  | THole         (* `?` *)

type lexed = { token: token; start: int; end_: int }

let is_ident_start c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

let is_ident_char c =
  is_ident_start c || (c >= '0' && c <= '9') || c = '-'

exception Lex_error of string * int

(* Tokenize a substring of `src` starting at `line_start` of length `len`.
   `line_start` is the absolute byte offset of the substring within the
   full source file — every returned token's positions are absolute. *)
let tokenize ~(src : string) ~(line_start : int) ~(len : int) : lexed list =
  let pos = ref 0 in
  let acc = ref [] in
  let push t s e = acc := { token = t; start = line_start + s; end_ = line_start + e } :: !acc in
  while !pos < len do
    let c = src.[line_start + !pos] in
    match c with
    | ' ' | '\t' -> incr pos
    | '(' -> push TLParen !pos (!pos + 1); incr pos
    | ')' -> push TRParen !pos (!pos + 1); incr pos
    | ':' -> push TColon !pos (!pos + 1); incr pos
    | '?' -> push THole !pos (!pos + 1); incr pos
    | _ when is_ident_start c ->
      let start = !pos in
      while !pos < len && is_ident_char src.[line_start + !pos] do
        incr pos
      done;
      let s = String.sub src (line_start + start) (!pos - start) in
      push (TIdent s) start !pos
    | _ ->
      raise (Lex_error (Printf.sprintf "unexpected character %C" c, line_start + !pos))
  done;
  List.rev !acc
