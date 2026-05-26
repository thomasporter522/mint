(* `mintc` (slice edition): a single binary that takes a `.mint` file,
   parses it, type-checks the OL, then runs the meta blocks through a
   Toploop session. Same shape as the main-branch experience — OCaml
   meta-code under the hood replaces the custom Mint interpreter. *)

let banner s = print_endline ("\n=== " ^ s ^ " ===")

let print_ol = Print.print_ol

(* === Witness-check helpers ==========================================
   After each construct phrase, the synthesized OCaml stores the
   schema's returned witnesses in `__mint_last_witnesses` and the
   matching decl names in `__mint_last_witness_names`. The kernel
   pulls both via `Toploop.getvalue`, walks each witness term with
   `Obj.Extension_constructor` to recover the constructor name + its
   args, builds an OL term, and runs `check_ol_term` against the
   decl's declared return type — mirroring main's runConstructSchema. *)

let strip_module_prefix (s : string) : string =
  match String.rindex_opt s '.' with
  | Some i -> String.sub s (i + 1) (String.length s - i - 1)
  | None -> s

(* Per-constructor info: the source name (with original Mint spelling
   — possibly lowercase, possibly with hyphens) plus the declared
   arity. Keyed by the MANGLED OCaml constructor name (which is what
   `Obj.Extension_constructor.name` returns).

   The kernel populates this from every postulate / construct decl
   before running phrases. We need the arity because extension-variant
   value blocks have a minimum size of 2 (a 0-arity constructor still
   allocates a 2-field block), so `Obj.size` isn't reliable. We need
   the source name because witness terms come back with the OCaml
   name, but the kernel's context indexes by Mint source name. *)
type ctor_info = { source_name : string; arity : int }
let constructor_info : (string, ctor_info) Hashtbl.t = Hashtbl.create 32

let () =
  (* Prelude-defined kernel-bridge constructors. `Param` is handled
     specially in `witness_term_to_ol` (it carries a string, not a
     term) so we don't register it here. *)
  Hashtbl.add constructor_info "MintHole"
    { source_name = "MintHole"; arity = 0 };
  Hashtbl.add constructor_info "MintMeta"
    { source_name = "MintMeta"; arity = 1 }

(* Convert an OCaml value of type `term` (the prelude's extensible
   variant) into an OL term, consulting the arity registry to read
   the right number of args. *)
let rec witness_term_to_ol (r : Obj.t) : Ast.ol =
  try
    let ext = Obj.Extension_constructor.of_val (Obj.obj r : Obj.t) in
    let raw = Obj.Extension_constructor.name ext in
    let name = strip_module_prefix raw in
    if name = "MintHole" then Ast.mk_ol Ast.OLHole
    else if name = "MintMeta" then
      let n = (Obj.magic (Obj.field r 1) : int) in
      Ast.mk_ol (Ast.OLMeta n)
    else if name = "Param" then
      let pname = (Obj.magic (Obj.field r 1) : string) in
      let sm : Ast.string_meta = { string = pname; meta = Ast.default_meta } in
      { value = Ast.OLAp (sm, []); meta = Ast.default_meta }
    else
      let info =
        match Hashtbl.find_opt constructor_info name with
        | Some i -> i
        | None -> { source_name = name; arity = 0 }
      in
      let args =
        if info.arity = 0 || Obj.is_int r then []
        else
          let acc = ref [] in
          for i = info.arity downto 1 do
            acc := witness_term_to_ol (Obj.field r i) :: !acc
          done;
          !acc
      in
      let sm : Ast.string_meta =
        { string = info.source_name; meta = Ast.default_meta }
      in
      { value = Ast.OLAp (sm, args); meta = Ast.default_meta }
  with _ -> Ast.mk_ol Ast.OLHole

let read_witnesses () : (string * Ast.ol) list =
  try
    let names : string list ref =
      Obj.magic (Toploop.getvalue "__mint_last_witness_names")
    in
    let ws : Obj.t list ref =
      Obj.magic (Toploop.getvalue "__mint_last_witnesses")
    in
    let rec zip xs ys = match xs, ys with
      | [], _ | _, [] -> []
      | x :: xs, y :: ys -> (x, witness_term_to_ol y) :: zip xs ys
    in
    zip !names !ws
  with _ -> []

let check_witness
    ~(ctx : Check.context)
    ~(subst_env : Check.witness_env)
    ~(decl : Ast.decl_line)
    ~(witness_ol : Ast.ol)
    : Error.t list =
  (* Build a witness-checking context by extending `ctx` with each
     param of the decl. Mirrors main's witnessCtx construction;
     param types are themselves resolved through `subst_env` so a
     peer decl can occur in a param type (rare but valid). *)
  let witness_ctx =
    List.fold_left (fun acc (a : Ast.decl_arg) ->
      let resolved_pty = Check.resolve_with_params subst_env a.decl_arg_type in
      let ty : Check.full_type = ([], resolved_pty) in
      Check.StringMap.add a.decl_arg_name.string (Check.OLBinding ty) acc
    ) ctx decl.args
  in
  (* Resolve the decl's expected type through subst_env too, so
     references to peer decls (and to this decl's own name) get
     substituted to their elaborated witnesses. *)
  let expected = Check.resolve_with_params subst_env decl.ret_type in
  let (info, state') =
    Check.check_ol_term Check.empty_elab_state
      witness_ctx (Some expected) witness_ol
  in
  (* Mirror check_decl_line: walk the elaborated witness for
     "Implicit/Coercion not fully solved" warnings. The witness can
     contain unsolved ghost metas that don't surface as `info.errors`
     but should still be flagged. Witnesses additionally require
     EVERY meta to be solved (user `?` in OL code is legit, but a
     `?` inside a schema-returned witness means an incomplete proof);
     so we also walk for any surviving non-ghost meta. *)
  let any_meta_unsolved (t : Ast.ol) : bool =
    let rec walk (t : Ast.ol) =
      let t = Check.follow state'.sols t in
      match t.value with
      | Ast.OLMeta _ -> true
      | Ast.OLAp (_, args) -> List.exists walk args
      | _ -> false
    in
    walk t
  in
  let unsolved_warns =
    match info.elaborated with
    | None -> []
    | Some elab ->
      let strip = Check.strip_implicits state'.sols witness_ctx in
      let (_, ghost_warns) =
        Check.extract_diagnostics strip state'.sols elab
      in
      let witness_incomplete_warns =
        if any_meta_unsolved elab && ghost_warns = [] then
          [Error.warn "Witness contains unsolved metavariables"
             decl.decl_meta.start decl.decl_meta.end_]
        else []
      in
      ghost_warns @ witness_incomplete_warns
  in
  List.map (fun (e : Error.t) -> {
    e with
    Error.from = decl.decl_meta.start;
    Error.to_  = decl.decl_meta.end_;
    message = Printf.sprintf "witness for %s: %s"
      decl.decl_name.string e.message;
  }) (info.errors @ unsolved_warns)

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
  if not (Driver.exec Translator.prelude) then begin
    prerr_endline "(prelude rejected)";
    exit 1
  end;

  (* The kernel needs the FINAL elaborated context to verify witnesses
     (witnesses can reference any decl in the program). `check_program`
     already returned `info` above; we re-do the per-block walk here
     to recover the cumulative context, since `info` collapsed it. *)
  let final_ctx =
    let (_, ctx') =
      List.fold_left (fun (info_acc, ctx_acc) b ->
        let (i, c) = Check.check_block ctx_acc b in
        (Check.merge_info info_acc i, c)
      ) (Check.empty_info, Check.initial_context) program
    in
    ctx'
  in

  (* Register the (source name, arity) of every constructor the
     program postulates or constructs. The witness-conversion walker
     uses arity to read the right number of fields, and source name
     to map back from OCaml's mangled identifier to the kernel's
     context. *)
  let register_decls (decls : Ast.decl_line list) =
    List.iter (fun (d : Ast.decl_line) ->
      let source = d.decl_name.string in
      let mangled = Translator.mangle_constructor source in
      Hashtbl.replace constructor_info mangled
        { source_name = source; arity = List.length d.args }
    ) decls
  in
  List.iter (function
    | Ast.Postulate pb ->
      register_decls (Translator.decls_of_lines pb.postulate_lines)
    | Ast.Construct cb ->
      register_decls (Translator.decls_of_lines cb.construct_lines)
    | Ast.MetaBlock _ -> ()
  ) program;

  (* Process blocks in order: translate, run, and after a Construct,
     read back its witnesses and run the OL elaborator against each
     decl's declared retType. This is main's runConstructSchema
     witness-check pass, with the schema source swapped from
     `Eval.runSchema` to the Toploop buffer. *)
  (* Replace a decl's arg / ret types with their FINAL elaborated forms
     from `final_ctx`. The translator emits OCaml constructor applications
     keyed by arity, so a user-written `eq lhs rhs` (with 2 leading
     implicits) must become `eq A B lhs rhs` in the synthesized signature
     — otherwise the OCaml `Eq` constructor sees 2 args, not 4, and the
     phrase fails to compile. *)
  let elaborate_decl (d : Ast.decl_line) : Ast.decl_line =
    match Check.StringMap.find_opt d.decl_name.string final_ctx with
    | Some (Check.OLBinding (params, ret)) ->
      let args =
        List.map2 (fun (a : Ast.decl_arg) (_, elab_ty) ->
          { a with decl_arg_type = elab_ty }
        ) d.args params
      in
      { d with args; ret_type = ret }
    | _ -> d
  in
  let elaborate_block (b : Ast.block) : Ast.block =
    match b with
    | Ast.Construct cb ->
      let lines =
        List.map (function
          | Ast.Decl d -> Ast.Decl (elaborate_decl d)
          | other -> other
        ) cb.construct_lines
      in
      Ast.Construct { cb with construct_lines = lines }
    | _ -> b
  in
  let witness_errors = ref [] in
  List.iter (fun b ->
    let b_for_translation = elaborate_block b in
    let block_phrases = Translator.block_to_phrases ~src ~path b_for_translation in
    List.iter (fun s ->
      if not (Driver.exec s) then begin
        prerr_endline "(phrase rejected)";
        exit 1
      end
    ) block_phrases;

    match b with
    | Ast.Construct cb ->
      let decls = Translator.decls_of_lines cb.construct_lines in
      let witness_map = read_witnesses () in
      List.iter (fun (n, w) ->
        Printf.printf "  - %s = %s\n" n (Print.print_ol w)
      ) witness_map;
      (* Build a block-wide substitution env BEFORE any witness check,
         so each witness sees every peer in the same construct block.
         Mirrors main's `initialSubstEnv` pre-pass. *)
      let subst_env =
        List.fold_left (fun acc (d : Ast.decl_line) ->
          match List.assoc_opt d.decl_name.string witness_map with
          | None -> acc
          | Some w ->
            let pnames = List.map (fun (a : Ast.decl_arg) ->
              a.decl_arg_name.string
            ) d.args in
            Check.StringMap.add d.decl_name.string (pnames, w) acc
        ) Check.empty_witness_env decls
      in
      List.iter (fun (d : Ast.decl_line) ->
        let name = d.decl_name.string in
        match List.assoc_opt name witness_map with
        | None -> ()
        | Some witness_ol ->
          let resolved_witness =
            Check.resolve_with_params subst_env witness_ol
          in
          let errs =
            check_witness ~ctx:final_ctx ~subst_env ~decl:d
              ~witness_ol:resolved_witness
          in
          witness_errors := !witness_errors @ errs
      ) decls
    | _ -> ()
  ) program;

  (match !witness_errors with
   | [] -> ()
   | errs ->
     banner "Witness type-check";
     let n_errs = List.length (List.filter Error.is_real errs) in
     let n_warns = List.length errs - n_errs in
     Printf.printf "%d error(s), %d warning(s):\n" n_errs n_warns;
     List.iter (fun e -> print_endline (Error.pp path src e)) errs;
     if n_errs > 0 then exit 1)
