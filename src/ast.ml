(* Mint OL AST — mirrors `reason/src/Term.re` in shape. Native OCaml
   version (snake_case names; no Melange decorators). The OL types are
   the only ones the kernel needs to manipulate; meta blocks pass
   through as opaque source strings handed to the Toploop session. *)

type ghost_kind = Implicit | Coerce

type meta = {
  parens: bool;
  start: int;
  end_: int;
  ghost: ghost_kind option;
}

let default_meta = { parens = false; start = -1; end_ = -1; ghost = None }
let as_ghost k m = { m with ghost = Some k }
let is_ghost m = match m.ghost with Some _ -> true | None -> false

(* A name carrying its own source range. Used wherever the kernel needs
   to keep an identifier's position separate from its enclosing form. *)
type string_meta = {
  string: string;
  meta: meta;
}

type c_ol =
  | OLHole
  | OLAp of string_meta * ol list
  | OLMeta of int
and ol = {
  value: c_ol;
  meta: meta;
}

let mk_ol v = { value = v; meta = default_meta }

(* `decl_arg`: a single named parameter in a decl. Grouped forms like
   `(a b : T)` desugar into multiple `decl_arg`s sharing a type. *)
type decl_arg = {
  decl_arg_name: string_meta;
  decl_arg_type: ol;
  decl_arg_meta: meta;
}

type decl_line = {
  decl_name: string_meta;
  args: decl_arg list;
  ret_type: ol;
  decl_meta: meta;
}

type tag_line = {
  tag: string;
  target: string;
  tag_meta: meta;
}

type ol_line =
  | Decl of decl_line
  | Tag of tag_line

type postulate_block = {
  postulate_meta: meta;
  postulate_lines: ol_line list;
}

type construct_block = {
  schema: string;
  schema_meta: meta;
  construct_lines: ol_line list;
}

(* Meta blocks carry raw OCaml source text, handed verbatim to the
   Toploop session. The kernel doesn't inspect this string — it only
   tracks the block's source range for diagnostic purposes. *)
type meta_block = {
  meta_block_meta: meta;
  source: string;
}

type block =
  | Postulate of postulate_block
  | MetaBlock of meta_block
  | Construct of construct_block

type program = block list
