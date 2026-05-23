(* `mintc` (slice edition): a single binary that takes a `.mint` file,
   parses it, type-checks the OL, then runs the meta blocks through a
   Toploop session. Same shape as the main-branch experience — OCaml
   meta-code under the hood replaces the custom Mint interpreter. *)

let banner s = print_endline ("\n=== " ^ s ^ " ===")

let print_ol = Print.print_ol

let print_decl (d : Ast.decl_line) =
  let arg_str =
    if d.args = [] then ""
    else " " ^ String.concat " " (List.map (fun (a : Ast.decl_arg) ->
      Printf.sprintf "(%s : %s)" a.decl_arg_name.string (print_ol a.decl_arg_type)
    ) d.args)
  in
  Printf.printf "  %s%s : %s\n" d.decl_name.string arg_str (print_ol d.ret_type)

let print_summary (prog : Ast.program) =
  List.iter (function
    | Ast.Postulate pb ->
      let n = List.length (Translator.decls_of_lines pb.postulate_lines) in
      Printf.printf "postulate (%d decl%s)\n"
        n (if n = 1 then "" else "s");
      List.iter (function
        | Ast.Decl d -> print_decl d
        | Ast.Tag t -> Printf.printf "  #%s %s\n" t.Ast.tag t.Ast.target
      ) pb.postulate_lines
    | Ast.MetaBlock mb ->
      let chars = String.length mb.source in
      let lines = List.length (String.split_on_char '\n' mb.source) in
      Printf.printf "meta (%d chars, ~%d lines)\n" chars lines
    | Ast.Construct cb ->
      let n = List.length (Translator.decls_of_lines cb.construct_lines) in
      Printf.printf "construct by %s (%d decl%s)\n"
        cb.schema n (if n = 1 then "" else "s");
      List.iter (function
        | Ast.Decl d -> print_decl d
        | Ast.Tag t -> Printf.printf "  #%s %s\n" t.Ast.tag t.Ast.target
      ) cb.construct_lines
  ) prog

let () =
  if Array.length Sys.argv < 2 then begin
    prerr_endline "usage: main FILE.mint";
    exit 2
  end;
  let path = Sys.argv.(1) in
  let (src, program) =
    try Parser.parse_file path
    with
    | Parser.Parse_error (msg, offset) ->
      let (line, col) =
        if offset < 0 then (0, 0)
        else
          let s = try
            let ic = open_in path in
            let n = in_channel_length ic in
            let b = Bytes.create n in
            really_input ic b 0 n; close_in ic;
            Bytes.to_string b
          with _ -> "" in
          Error.line_col s offset
      in
      Printf.eprintf "%s:%d:%d: parse error: %s\n" path line col msg;
      exit 1
    | Lexer.Lex_error (msg, offset) ->
      let s = try
        let ic = open_in path in
        let n = in_channel_length ic in
        let b = Bytes.create n in
        really_input ic b 0 n; close_in ic;
        Bytes.to_string b
      with _ -> "" in
      let (line, col) = Error.line_col s offset in
      Printf.eprintf "%s:%d:%d: lex error: %s\n" path line col msg;
      exit 1
  in

  banner "Parsed blocks";
  print_summary program;

  banner "OL elaboration";
  let info = Check.check_program program in
  let n_errs = List.length (List.filter Error.is_real info.errors) in
  let n_warns = List.length info.errors - n_errs in
  let n_holes = List.length info.holes in
  Printf.printf "%d error(s), %d warning(s), %d hole(s)\n"
    n_errs n_warns n_holes;
  List.iter (fun e ->
    print_endline (Error.pp path src e)
  ) info.errors;
  (* Show each hole's goal type at its source position. IDE consumers
     would read this same `holes` field structurally; we just print it. *)
  List.iter (fun (h : Check.hole_info) ->
    let (line, col) = Error.line_col src h.offset in
    Printf.printf "%s:%d:%d: hole: goal = %s\n"
      path line col (print_ol h.goal)
  ) info.holes;
  (* Inlay hints: implicit-arg insertions and (when wired) coercion
     wrappings. The kernel anchors each hint at a byte offset; here we
     emit a line per hint that the IDE plugin parses. *)
  List.iter (fun (h : Check.inlay_hint) ->
    let (line, col) = Error.line_col src h.hint_offset in
    let kind = match h.hint_kind with
      | Ast.Implicit -> "implicit"
      | Ast.Coerce -> "coerce"
    in
    Printf.printf "%s:%d:%d: hint %s: %s\n"
      path line col kind h.hint_tooltip
  ) info.inlay_hints;
  if Error.has_real info.errors then begin
    prerr_endline "\nelaboration failed; skipping meta execution.";
    exit 1
  end;

  banner "Translated source";
  print_string Translator.prelude;
  List.iter (fun b ->
    List.iter print_string (Translator.block_to_phrases ~src ~path b)
  ) program;

  Driver.init ();
  banner "Executing through Toploop";
  let phrases =
    Translator.prelude
    :: List.concat_map (Translator.block_to_phrases ~src ~path) program
  in
  List.iter (fun src ->
    if not (Driver.exec src) then begin
      prerr_endline "(phrase rejected)";
      exit 1
    end
  ) phrases
