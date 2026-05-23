(* Mint parser. Block-level structure (postulate / meta / construct
   blocks terminated by `end`) is recognized line-by-line; OL terms
   inside decl lines go through the recursive-descent in `parse_ol_term`.

   This isn't a faithful Mint parser — the real one is in Lezer and
   handles a lot more. Enough for the slice to consume realistic
   postulate / construct blocks. *)

open Ast

exception Parse_error of string * int

let trim = String.trim

let starts_with prefix s =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let strip_prefix prefix s =
  let lp = String.length prefix in
  trim (String.sub s lp (String.length s - lp))

(* === Token-stream parsing for a single line =========================== *)

(* A small mutable stream over a token list. Consumers `peek` and
   `advance`; positions on each token are absolute byte offsets in the
   source file. *)
type ts = { mutable toks: Lexer.lexed list }

let peek (s : ts) = match s.toks with
  | [] -> None
  | t :: _ -> Some t

let advance (s : ts) = match s.toks with
  | [] -> ()
  | _ :: rest -> s.toks <- rest

let expect_token (s : ts) (kind : Lexer.token) (msg : string) : Lexer.lexed =
  match peek s with
  | Some t when t.token = kind -> advance s; t
  | Some t -> raise (Parse_error (msg, t.start))
  | None -> raise (Parse_error (msg ^ " (got EOF)", -1))

(* parse_ol_atom: identifier | "?" | "(" ol_term ")" *)
let rec parse_ol_atom (s : ts) : ol option =
  match peek s with
  | Some { token = TIdent name; start; end_ } ->
    advance s;
    let sm = { string = name; meta = { default_meta with start; end_ } } in
    Some {
      value = OLAp (sm, []);
      meta = { default_meta with start; end_ };
    }
  | Some { token = THole; start; end_ } ->
    advance s;
    Some { value = OLHole; meta = { default_meta with start; end_ } }
  | Some { token = TLParen; start = lp_start; _ } ->
    advance s;
    let inner = parse_ol_term s in
    let rp = expect_token s TRParen "expected `)`" in
    (match inner with
     | Some t ->
       let m = { t.meta with parens = true; start = lp_start; end_ = rp.end_ } in
       Some { t with meta = m }
     | None ->
       raise (Parse_error ("expected expression inside parens", lp_start)))
  | _ -> None

(* parse_ol_term: atom (atom)*  — a juxtaposition becomes an OLAp on the
   head's name. If the head is a hole/paren, applied args attach without
   a name (degenerate). *)
and parse_ol_term (s : ts) : ol option =
  match parse_ol_atom s with
  | None -> None
  | Some head ->
    let rec collect acc =
      match parse_ol_atom s with
      | None -> List.rev acc
      | Some a -> collect (a :: acc)
    in
    let args = collect [] in
    if args = [] then Some head
    else
      match head.value with
      | OLAp (sm, []) ->
        let last = List.nth args (List.length args - 1) in
        let combined_meta =
          { head.meta with start = head.meta.start; end_ = last.meta.end_ }
        in
        Some { value = OLAp (sm, args); meta = combined_meta }
      | _ ->
        (* Head isn't a name; degenerate apply — wrap with a dummy head
           so downstream code doesn't crash. Real Mint would have caught
           this in the grammar. *)
        Some head

(* parse_arg_group: "(" ident+ ":" ol_term ")", returning the list of
   decl_args (one per name, sharing the parsed type). *)
let parse_arg_group (s : ts) : decl_arg list =
  let lp = expect_token s TLParen "expected `(`" in
  let names = ref [] in
  let rec take_names () =
    match peek s with
    | Some { token = TIdent name; start; end_ } ->
      advance s;
      names := (name, start, end_) :: !names;
      take_names ()
    | _ -> ()
  in
  take_names ();
  if !names = [] then
    raise (Parse_error ("expected one or more identifiers in arg group", lp.start));
  let _ = expect_token s TColon "expected `:` in arg group" in
  let ty = match parse_ol_term s with
    | Some t -> t
    | None -> raise (Parse_error ("expected type in arg group", lp.start))
  in
  let rp = expect_token s TRParen "expected `)`" in
  let group_meta = { default_meta with start = lp.start; end_ = rp.end_ } in
  List.rev_map (fun (n, ns, ne) ->
    {
      decl_arg_name = { string = n; meta = { default_meta with start = ns; end_ = ne } };
      decl_arg_type = ty;
      decl_arg_meta = group_meta;
    }
  ) !names

(* parse_decl_line: name arg* `:` ret_type *)
let parse_decl_line (toks : Lexer.lexed list) (line_meta : meta) : decl_line =
  let s = { toks } in
  let name_tok = match peek s with
    | Some t -> t
    | None -> raise (Parse_error ("empty decl line", line_meta.start))
  in
  let name = match name_tok.token with
    | TIdent n ->
      advance s;
      { string = n; meta = { default_meta with start = name_tok.start; end_ = name_tok.end_ } }
    | _ ->
      raise (Parse_error ("decl line must start with an identifier", name_tok.start))
  in
  let rec collect_args acc =
    match peek s with
    | Some { token = TLParen; _ } ->
      let group = parse_arg_group s in
      collect_args (acc @ group)
    | _ -> acc
  in
  let args = collect_args [] in
  let _ = expect_token s TColon "expected `:` before return type" in
  let ret_type = match parse_ol_term s with
    | Some t -> t
    | None -> raise (Parse_error ("expected return type", line_meta.start))
  in
  (match peek s with
   | Some t -> raise (Parse_error ("unexpected trailing tokens in decl line", t.start))
   | None -> ());
  { decl_name = name; args; ret_type; decl_meta = line_meta }

(* === Tag-line parsing ============================================ *)

(* `#tagname target` — a tag-line attaches a tag to an already-declared
   constructor. Returns a `tag_line` AST node. *)
let parse_tag_line (trimmed : string) (line_meta : meta) : tag_line =
  let parts = String.split_on_char ' '
    (String.concat " " (String.split_on_char '\t' trimmed))
  in
  let parts = List.filter (fun s -> s <> "") parts in
  match parts with
  | [hashed; target] when String.length hashed > 0 && hashed.[0] = '#' ->
    let tag = String.sub hashed 1 (String.length hashed - 1) in
    { tag; target; tag_meta = line_meta }
  | _ ->
    raise (Parse_error
      ("expected `#tagname target`, got: " ^ trimmed, line_meta.start))

(* === Block-level file parsing ====================================== *)

type parse_state =
  | Outside
  | InPostulate of {
      start: int;
      lines: ol_line list;
      pending: Lexer.lexed list;
      base_indent: int;  (* indent of pending's first physical line *)
    }
  | InMeta of {
      start: int;
      buf: Buffer.t;
    }
  | InConstruct of {
      start: int;
      schema: string;
      schema_start: int;
      schema_end: int;
      lines: ol_line list;
      pending: Lexer.lexed list;
      base_indent: int;
    }

let span_meta (toks : Lexer.lexed list) : meta =
  match toks, List.rev toks with
  | first :: _, last :: _ ->
    { default_meta with start = first.start; end_ = last.end_ }
  | _ -> default_meta

(* Count leading whitespace (spaces and tabs) of a physical source line.
   Used as the per-line indent for continuation detection. *)
let line_indent (line : string) : int =
  let n = String.length line in
  let rec go i =
    if i >= n then i
    else match line.[i] with
      | ' ' | '\t' -> go (i + 1)
      | _ -> i
  in
  go 0

(* Walk the source file once, advancing an offset and yielding a `program`.
   Each block is delimited at the start by `postulate` / `meta` / `construct by NAME`
   keywords appearing as the first non-whitespace of a line, and at the
   end by `end` on its own line. *)
let parse_source ~(src : string) : program =
  let n = String.length src in

  (* Yield each (line_start, line_end_exclusive_of_newline, line_string)
     where line_end is the position of the trailing '\n' (or n at EOF). *)
  let rec iter_lines pos f =
    if pos >= n then ()
    else
      let rec find_eol i =
        if i >= n then i
        else if src.[i] = '\n' then i
        else find_eol (i + 1)
      in
      let eol = find_eol pos in
      let line = String.sub src pos (eol - pos) in
      f ~line_start:pos ~line_end:eol ~line;
      iter_lines (eol + 1) f
  in

  let state = ref Outside in
  let acc = ref [] in

  let push_block b = acc := b :: !acc in

  iter_lines 0 (fun ~line_start ~line_end ~line ->
    let t = trim line in
    let line_meta = { default_meta with start = line_start; end_ = line_end } in
    let outside_meta = match !state with InMeta _ -> false | _ -> true in
    if outside_meta && (t = "" || starts_with "//" t) then ()
    else
      match !state with
      | Outside ->
        if starts_with "postulate" t then
          state := InPostulate {
            start = line_start; lines = []; pending = []; base_indent = 0
          }
        else if starts_with "meta" t then
          state := InMeta { start = line_start; buf = Buffer.create 256 }
        else if starts_with "construct by " t then begin
          let leading_ws =
            let rec go i = if i < String.length line && (line.[i] = ' ' || line.[i] = '\t') then go (i + 1) else i in
            go 0
          in
          let kw_off = leading_ws + String.length "construct by " in
          let schema_start = line_start + kw_off in
          let schema = strip_prefix "construct by " t in
          let schema_end = schema_start + String.length schema in
          state := InConstruct {
            start = line_start; schema; schema_start; schema_end;
            lines = []; pending = []; base_indent = 0
          }
        end else
          raise (Parse_error ("unexpected line outside any block", line_start))
      | InPostulate r ->
        let indent = line_indent line in
        (* A pending decl is complete when we hit either `end` or a new
           line at indent <= the pending decl's first-line indent. *)
        let finalize_pending lines pending =
          if pending = [] then lines
          else
            let decl = parse_decl_line pending (span_meta pending) in
            Decl decl :: lines
        in
        if t = "end" then begin
          let lines = finalize_pending r.lines r.pending in
          push_block (Postulate {
            postulate_meta = { default_meta with start = r.start; end_ = line_end };
            postulate_lines = List.rev lines;
          });
          state := Outside
        end else begin
          let (lines0, pending0, base0) =
            if r.pending <> [] && indent <= r.base_indent then
              (finalize_pending r.lines r.pending, [], 0)
            else
              (r.lines, r.pending, r.base_indent)
          in
          if starts_with "#" t then begin
            if pending0 <> [] then
              raise (Parse_error
                ("tag line cannot continue a decl; outdent it", line_start));
            let tag = parse_tag_line t line_meta in
            state := InPostulate {
              start = r.start;
              lines = Tag tag :: lines0;
              pending = pending0;
              base_indent = base0;
            }
          end else begin
            let toks =
              Lexer.tokenize ~src ~line_start ~len:(line_end - line_start)
            in
            let (pending', base') =
              if pending0 = [] then (toks, indent)
              else (pending0 @ toks, base0)
            in
            state := InPostulate {
              start = r.start;
              lines = lines0;
              pending = pending';
              base_indent = base';
            }
          end
        end
      | InMeta r ->
        if t = "end" then begin
          push_block (MetaBlock {
            meta_block_meta = { default_meta with start = r.start; end_ = line_end };
            source = Buffer.contents r.buf;
          });
          state := Outside
        end else begin
          Buffer.add_string r.buf line;
          Buffer.add_char r.buf '\n'
        end
      | InConstruct r ->
        let indent = line_indent line in
        let finalize_pending lines pending =
          if pending = [] then lines
          else
            let decl = parse_decl_line pending (span_meta pending) in
            Decl decl :: lines
        in
        if t = "end" then begin
          let lines = finalize_pending r.lines r.pending in
          push_block (Construct {
            schema = r.schema;
            schema_meta = { default_meta with start = r.schema_start; end_ = r.schema_end };
            construct_lines = List.rev lines;
          });
          state := Outside
        end else begin
          let (lines0, pending0, base0) =
            if r.pending <> [] && indent <= r.base_indent then
              (finalize_pending r.lines r.pending, [], 0)
            else
              (r.lines, r.pending, r.base_indent)
          in
          if starts_with "#" t then begin
            if pending0 <> [] then
              raise (Parse_error
                ("tag line cannot continue a decl; outdent it", line_start));
            let tag = parse_tag_line t line_meta in
            state := InConstruct {
              start = r.start;
              schema = r.schema;
              schema_start = r.schema_start;
              schema_end = r.schema_end;
              lines = Tag tag :: lines0;
              pending = pending0;
              base_indent = base0;
            }
          end else begin
            let toks =
              Lexer.tokenize ~src ~line_start ~len:(line_end - line_start)
            in
            let (pending', base') =
              if pending0 = [] then (toks, indent)
              else (pending0 @ toks, base0)
            in
            state := InConstruct {
              start = r.start;
              schema = r.schema;
              schema_start = r.schema_start;
              schema_end = r.schema_end;
              lines = lines0;
              pending = pending';
              base_indent = base';
            }
          end
        end
  );

  (match !state with
   | Outside -> ()
   | _ -> raise (Parse_error ("unterminated block (missing `end`)", n)));

  List.rev !acc

let parse_file (path : string) : string * program =
  let ic = open_in path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  let src = Bytes.to_string buf in
  (src, parse_source ~src)
