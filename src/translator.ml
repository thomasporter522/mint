(* Mint AST → OCaml top-level phrases. Postulate / construct decls
   become `type term += ...` extensions whose arity matches the OL
   decl's args. Meta blocks pass their source through. Construct
   blocks additionally synthesize a kernel-side call to the named
   schema. Each emitted phrase is preceded by a `# line "file"`
   directive so Toploop's error messages reference the original
   Mint source. *)

open Ast

(* Prelude — opens `term` and provides the kernel-bridge `Mint` module.
   No user term-formers are seeded. The `Mint`-prefixed constructors
   `MintHole` / `MintMeta` represent elaborator-internal placeholders
   that the kernel may translate into terms when a witness contains an
   unsolved meta or an explicit `?`. Their names are deliberately long
   to keep them out of the way of user-declared names; meta code
   normally interacts via the helper functions (`hole`, `is_hole`,
   `meta`, `is_meta`, `meta_id`).

   `canonical` is stubbed; the real implementation will shell out to
   the canonical solver as in main. *)
let prelude = {ocaml|
type term = ..

module Mint = struct
  (* `Param` represents a reference to a decl param from inside a
     signature's `ret` or `params` field — e.g. for
       `ap-I (x : D) : eq D D (ap I x) x`
     the `ret` contains two references to the param `x`. Since `x`
     isn't bound as an OCaml value at the call site, we emit
     `Param "x"` instead; the kernel decodes it back to the OL
     identifier `x` when the witness is read. *)
  type term += MintHole | MintMeta of int | Param of string

  type signature = {
    name: string;
    params: (string * term) list;
    ret: term;
    tags: string list;
  }

  let hole () : term = MintHole
  let is_hole (t : term) : bool =
    match t with MintHole -> true | _ -> false

  let meta (n : int) : term = MintMeta n
  let is_meta (t : term) : bool =
    match t with MintMeta _ -> true | _ -> false
  let meta_id (t : term) : int option =
    match t with MintMeta n -> Some n | _ -> None

  let param (s : string) : term = Param s
  let is_param (t : term) : bool =
    match t with Param _ -> true | _ -> false
  let param_name (t : term) : string option =
    match t with Param s -> Some s | _ -> None

  let canonical (_ctx : signature list) (_goal : term)
      : (term, string) result =
    Error "canonical solver not yet wired in this build"

end
;;
open Mint
;;
(* Witness transport. The synthesized construct phrase stores each
   schema's returned witnesses in `__mint_last_witnesses`; the kernel
   reads them with `Toploop.getvalue` and walks each one via
   `Obj.Extension_constructor` introspection to recover OL terms for
   the witness-check pass (mirrors main's runConstructSchema, with the
   `Eval.runSchema` source replaced by Toploop). The companion ref
   carries the matching decl names so the kernel can pair them up. *)
let __mint_last_witnesses : term list ref = ref []
;;
let __mint_last_witness_names : string list ref = ref []
;;
|ocaml}

(* === OL → OCaml-source-expression =====================================
   Renders an OL term as an OCaml expression of type `term`. A bare
   identifier becomes itself (presumed in scope from a prior postulate
   extension). An applied form `f a b` becomes `F (a) (b)` — each arg
   parenthesised so precedence doesn't bite. Holes and unsolved metas
   shouldn't reach here for a successfully-elaborated program; if they
   do we fall back to `(failwith "...")` so the synthesized phrase
   still type-checks. *)
(* Mint identifiers can be lowercase or hyphenated (e.g., `eq`,
   `cong-ap`); OCaml constructors must start with an uppercase letter
   and can't contain `-`. We mangle: capitalize the first letter,
   replace hyphens with underscores. Schema (and meta-let) names are
   identifiers, not constructors, so they keep their case but still
   need hyphens replaced. *)
let mangle_identifier (s : string) : string =
  String.map (fun c -> if c = '-' then '_' else c) s

(* Mint identifiers carry meaningful case (`Unit` ≠ `unit`) but OCaml
   constructors must start uppercase, so naive capitalisation collides.
   We track which mangled names have been claimed and append `_2`,
   `_3`, … on later collisions. First-come wins — typically the
   postulate decl (processed before its construct decl), so a schema
   referencing `Unit` keeps pointing at the postulate's constructor.

   `mangled_of_source` is the forward map (source → claimed mangled
   name); the reverse is kept in `mintc`'s `constructor_info` for the
   witness round-trip. *)
let mangled_of_source : (string, string) Hashtbl.t = Hashtbl.create 32
let claimed_mangled  : (string, unit)   Hashtbl.t = Hashtbl.create 32

let mangle_constructor (s : string) : string =
  match Hashtbl.find_opt mangled_of_source s with
  | Some m -> m
  | None ->
    let base = String.capitalize_ascii (mangle_identifier s) in
    let rec pick candidate n =
      if Hashtbl.mem claimed_mangled candidate
      then pick (base ^ "_" ^ string_of_int n) (n + 1)
      else candidate
    in
    let final = pick base 2 in
    Hashtbl.add mangled_of_source s final;
    Hashtbl.add claimed_mangled final ();
    final

module StringSet = Set.Make(String)

(* `Foo (a, b, c)` not `Foo (a) (b) (c)`: OCaml constructors with
   multiple args take a tuple, not curried application.

   `param_set` collects the names that should be emitted as
   `Mint.param "x"` rather than as a global constructor. The
   signature builder for each decl passes its own param names so
   references to them resolve through the kernel's witness decoder
   instead of failing as unbound OCaml identifiers. *)
let rec ol_to_ocaml_expr (param_set : StringSet.t) (t : ol) : string =
  match t.value with
  | OLHole -> "(Mint.hole ())"
  | OLMeta n -> Printf.sprintf "(Mint.meta %d)" n
  | OLAp (f, []) when StringSet.mem f.string param_set ->
    Printf.sprintf "(Mint.param %S)" f.string
  | OLAp (f, []) -> mangle_constructor f.string
  | OLAp (f, args) ->
    let arg_strs = List.map (ol_to_ocaml_expr param_set) args in
    Printf.sprintf "%s (%s)"
      (mangle_constructor f.string)
      (String.concat ", " arg_strs)

(* === Postulate / construct constructor declaration =================== *)

(* `type term += Foo | Suc of term | Eq of term * term` — arity matches
   each decl's arg count. *)
let postulate_phrase_of_decls (decls : decl_line list) : string =
  let arm (d : decl_line) =
    let name = mangle_constructor d.decl_name.string in
    match d.args with
    | [] -> "  | " ^ name
    | args ->
      let n = List.length args in
      let term_args = String.concat " * " (List.init n (fun _ -> "term")) in
      Printf.sprintf "  | %s of %s" name term_args
  in
  let arms = String.concat "\n" (List.map arm decls) in
  "type term +=\n" ^ arms ^ "\n;;\n"

let decls_of_lines (lines : ol_line list) : decl_line list =
  List.filter_map (function Decl d -> Some d | Tag _ -> None) lines

let tags_of_lines (lines : ol_line list) : tag_line list =
  List.filter_map (function Tag t -> Some t | Decl _ -> None) lines

(* === Signature value emitted for the schema invocation ===============
   Each decl becomes `{ name; params; ret; tags }`. Params and ret use
   the real (elaborated) OL types via `ol_to_ocaml_expr`. Tag lines
   attached to a target are looked up by name. *)
let signature_expr ~(all_tags : tag_line list) (d : decl_line) : string =
  let param_set =
    List.fold_left (fun acc (a : decl_arg) ->
      StringSet.add a.decl_arg_name.string acc
    ) StringSet.empty d.args
  in
  let params_src =
    if d.args = [] then "[]"
    else
      let pairs = List.map (fun (a : decl_arg) ->
        Printf.sprintf "(%S, %s)"
          a.decl_arg_name.string
          (ol_to_ocaml_expr param_set a.decl_arg_type)
      ) d.args in
      "[ " ^ String.concat "; " pairs ^ " ]"
  in
  let tags_for_this =
    List.filter (fun (t : tag_line) -> t.target = d.decl_name.string) all_tags
  in
  let tags_src =
    if tags_for_this = [] then "[]"
    else
      let qs = List.map (fun (t : tag_line) ->
        Printf.sprintf "%S" t.tag
      ) tags_for_this in
      "[ " ^ String.concat "; " qs ^ " ]"
  in
  Printf.sprintf
    "{ name = %S; params = %s; ret = %s; tags = %s }"
    d.decl_name.string
    params_src
    (ol_to_ocaml_expr param_set d.ret_type)
    tags_src

let construct_phrase
    ~(schema : string)
    ~(decls : decl_line list)
    ~(tags : tag_line list)
    : string =
  let type_ext = postulate_phrase_of_decls decls in
  let n = List.length decls in
  let sig_list =
    "[ " ^ String.concat "; " (List.map (signature_expr ~all_tags:tags) decls)
    ^ " ]"
  in
  let decl_names =
    "[ "
    ^ String.concat "; "
        (List.map (fun (d : decl_line) -> Printf.sprintf "%S" d.decl_name.string) decls)
    ^ " ]"
  in
  let header =
    Printf.sprintf "[construct by %s] dispatching %d signature(s)"
      schema n
  in
  let call =
    Printf.sprintf {ocaml|
let () =
  __mint_last_witnesses := [];
  __mint_last_witness_names := %s;
  print_endline %S;
  match %s [] %s with
  | Ok witnesses ->
    __mint_last_witnesses := witnesses;
    Printf.printf "  schema returned %%d witness(es)\n" (List.length witnesses)
  | Error msg ->
    Printf.printf "  schema returned error: %%s\n" msg
;;
|ocaml}
      decl_names header (mangle_identifier schema) sig_list
  in
  type_ext ^ call

(* === Reason → OCaml conversion =====================================
   Mint meta blocks accept either OCaml or Reason syntax. We pipe the
   source through `refmt --parse re --print ml`; on success we use the
   OCaml output, on failure (refmt unhappy, or refmt not installed) we
   fall back to passing the source through verbatim — handling the
   common case where the user just wrote OCaml. *)
let try_refmt (input : string) : string option =
  try
    let cmd = "refmt --parse re --print ml 2>/dev/null" in
    let (ic, oc) = Unix.open_process cmd in
    output_string oc input;
    close_out oc;
    let buf = Buffer.create (String.length input) in
    (try
       while true do
         Buffer.add_char buf (input_char ic)
       done
     with End_of_file -> ());
    let status = Unix.close_process (ic, oc) in
    match status with
    | Unix.WEXITED 0 ->
      let out = Buffer.contents buf in
      if out = "" then None else Some out
    | _ -> None
  with _ -> None

(* === Source-position directive ====================================== *)

let line_directive ~(src : string) ~(path : string) ~(offset : int) : string =
  let (line, _) = Error.line_col src offset in
  Printf.sprintf "# %d %S\n" line path

(* The directive for a block points at the line where the kernel-relevant
   content starts, so Toploop errors land at the correct Mint line:

   • Postulate / construct: the keyword line itself. The synthesized
     `type term += ...` phrase will be reported on/around that line.
   • Meta: the line AFTER the `meta` keyword — that's where user code
     actually starts. *)
let block_to_phrases
    ~(src : string)
    ~(path : string)
    (b : block) : string list =
  match b with
  | Postulate pb ->
    let directive = line_directive ~src ~path ~offset:pb.postulate_meta.start in
    [ directive ^ postulate_phrase_of_decls (decls_of_lines pb.postulate_lines) ]
  | MetaBlock mb ->
    let (kw_line, _) = Error.line_col src mb.meta_block_meta.start in
    let directive = Printf.sprintf "# %d %S\n" (kw_line + 1) path in
    (* Try Reason → OCaml first; if refmt rejects (probably because the
       user wrote OCaml directly) fall back to using the source as-is.
       Note that for Reason input, refmt may reformat lines, so error
       positions within the meta block are approximate. *)
    let body =
      match try_refmt mb.source with
      | Some converted -> converted
      | None -> mb.source
    in
    (* Make sure the body ends with a newline + `;;` so the next
       directive lands on its own line and Toploop sees a phrase
       boundary. *)
    let sep = if String.length body > 0 && body.[String.length body - 1] = '\n'
              then ";;\n" else "\n;;\n" in
    [ directive ^ body ^ sep ]
  | Construct cb ->
    let directive = line_directive ~src ~path ~offset:cb.schema_meta.start in
    [ directive
      ^ construct_phrase
          ~schema:cb.schema
          ~decls:(decls_of_lines cb.construct_lines)
          ~tags:(tags_of_lines cb.construct_lines) ]
