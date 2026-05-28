(* OL elaboration kernel. Native port of `reason/src/Check.re`'s OL-only
   surface (same algorithm; native OCaml syntax). Returns errors and
   hole info; does not produce inlay hints, completeness markers, or
   coerce-search results — those return when integration with the
   meta-runtime stabilises. *)

open Ast

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

(* === Typing context ============================================== *)

(* A binding's "full type" is its parameter list (each param optionally
   named for substitution into later param types) plus its return type.
   Atomic bindings have empty params and put their kind in `ret`. *)
type full_type = (string option * ol) list * ol

type binding =
  | OLBinding of full_type

type context = binding StringMap.t

let empty_context : context = StringMap.empty

(* The kernel ships with zero built-in term-formers. Every name in an OL
   term must come from a user-written postulate or construct decl. The
   self-typed atom that bootstraps a Mint file (commonly written
   `Sort : Sort`) is just a regular user declaration — its name is the
   user's choice. *)
let initial_context : context = empty_context

(* === Per-decl elaboration state ==================================
   Mirrors main's `elabState`:
   • `sols`        — meta id → solution term.
   • `meta_types`  — meta id → expected type at allocation. Drives
                     type-level propagation in `unify`: when a meta is
                     solved to a non-meta term, its recorded expected
                     type gets unified against the solving term's
                     computed type, which can transitively solve other
                     metas.
   • `next_meta`   — counter for fresh ids. *)
type elab_state = {
  sols: ol IntMap.t;
  meta_types: ol IntMap.t;
  next_meta: int;
}

let empty_elab_state : elab_state = {
  sols = IntMap.empty;
  meta_types = IntMap.empty;
  next_meta = 0;
}

(* Fresh meta with a recorded expected type. No ghost marker — used
   for user-written `?` holes, which the IDE already surfaces directly
   (the `?` is visible in source) so no inlay hint is emitted at that
   position. *)
let mk_meta (state : elab_state) (expected_ty : ol) (m : meta) : ol * elab_state =
  let id = state.next_meta in
  let t = { value = OLMeta id; meta = m } in
  (t, {
    sols = state.sols;
    meta_types = IntMap.add id expected_ty state.meta_types;
    next_meta = id + 1;
  })

(* Fresh meta with a recorded expected type AND a ghost marker — used
   at auto-insertion sites (leading-arg implicits at constructor calls,
   future coerce wrappings). The ghost marker is what `extract_hints`
   watches for when emitting inlay hints. *)
let mk_ghost_meta
    (kind : ghost_kind) (state : elab_state) (expected_ty : ol) (m : meta)
    : ol * elab_state =
  let id = state.next_meta in
  let t = { value = OLMeta id; meta = as_ghost kind m } in
  (t, {
    sols = state.sols;
    meta_types = IntMap.add id expected_ty state.meta_types;
    next_meta = id + 1;
  })

let rec follow (sols : ol IntMap.t) (t : ol) : ol =
  match t.value with
  | OLMeta id ->
    (match IntMap.find_opt id sols with
     | Some t' -> follow sols t'
     | None -> t)
  | _ -> t

let rec zonk (sols : ol IntMap.t) (t : ol) : ol =
  let t' = follow sols t in
  match t'.value with
  | OLAp (f, args) -> { t' with value = OLAp (f, List.map (zonk sols) args) }
  | _ -> t'

let rec occurs (sols : ol IntMap.t) (id : int) (t : ol) : bool =
  let t' = follow sols t in
  match t'.value with
  | OLMeta id' -> id = id'
  | OLAp (_, args) -> List.exists (occurs sols id) args
  | _ -> false

(* Externalize a term by zonking through solutions and replacing any
   surviving (unsolved) metavariable with a hole. This is what main's
   `zonkAndForgetMetas` does: per-decl elaboration uses local meta IDs
   that have no meaning outside that decl, so when the result lands in
   another decl's context we forget the IDs and let the hole act as a
   wildcard under unification. *)
let rec zonk_and_forget (sols : ol IntMap.t) (t : ol) : ol =
  let t' = follow sols t in
  match t'.value with
  | OLMeta _ -> { t' with value = OLHole }
  | OLAp (f, args) ->
    { t' with value = OLAp (f, List.map (zonk_and_forget sols) args) }
  | _ -> t'

(* True if a term contains any hole-shaped subterm (user hole, synthesised
   hole, or unresolved meta). Used by per-decl completeness: a decl is
   not "type-complete" if its elaborated signature still has holes. *)
let rec ol_has_holes (t : ol) : bool =
  match t.value with
  | OLHole | OLMeta _ -> true
  | OLAp (_, args) -> List.exists ol_has_holes args

(* === Context lookup ============================================== *)

type lookup_result =
  | NotFound
  | FoundOL of full_type

let lookup_ctx (ctx : context) (name : string) : lookup_result =
  match StringMap.find_opt name ctx with
  | None -> NotFound
  | Some (OLBinding ft) -> FoundOL ft

(* Collect names of OL identifiers in `t` that resolve to OL bindings
   in `outer_ctx`. Local-only references (e.g. to a decl's own params)
   are filtered out — they aren't dependencies for completeness. *)
let ol_collect_refs (t : ol) (outer_ctx : context) : string list =
  let rec go acc (t : ol) =
    match t.value with
    | OLAp (f, args) ->
      let acc =
        match StringMap.find_opt f.string outer_ctx with
        | Some (OLBinding _) -> f.string :: acc
        | None -> acc
      in
      List.fold_left go acc args
    | OLHole | OLMeta _ -> acc
  in
  go [] t

(* Per-program completeness tracking. Each top-level decl is marked
   `true` once it elaborates without holes / errors AND each of its
   external refs (resolved against the outer context) is itself
   marked complete. Reset at program start; consulted by
   `all_refs_complete` and by the IDE's block-completeness ✓. *)
module StringSet = Set.Make(String)
let completeness_ref : (string, bool) Hashtbl.t = Hashtbl.create 32
let reset_completeness () = Hashtbl.reset completeness_ref

(* True iff every name in `refs` is marked complete. Names not yet
   registered are treated as incomplete — forward references inside a
   block are deferred until block-finalization, see `finalize_block`. *)
let all_refs_complete (refs : string list) : bool =
  List.for_all (fun name ->
    match Hashtbl.find_opt completeness_ref name with
    | Some true -> true
    | _ -> false
  ) refs

(* Single-character marker for the coercion-subject slot in
   `extract_diagnostics`. Matches main's `boxChar` (U+25A1, "□"). *)
let box_char = "\xE2\x96\xA1"

(* === Substitution: resolve named params in later param types ===== *)

type env = ol StringMap.t
let empty_env : env = StringMap.empty

let rec resolve (env : env) (t : ol) : ol =
  match t.value with
  | OLAp (f, args) ->
    (match StringMap.find_opt f.string env, args with
     | Some sub, [] -> sub
     | _ -> { t with value = OLAp (f, List.map (resolve env) args) })
  | _ -> t

(* Witness substitution. Maps each name to (param_names, witness_body).
   For parameterless decls, param_names is `[]`. For a parameterised
   decl `(f (x:A))` with witness `w`, resolving `(f arg)` substitutes
   `x := arg` inside `w`. Used by `run_construct_schema` so each
   witness sees its block-peer witnesses simultaneously (mutual
   recursion across the block). *)
type witness_env = (string list * ol) StringMap.t
let empty_witness_env : witness_env = StringMap.empty

let rec resolve_with_params (wenv : witness_env) (t : ol) : ol =
  if StringMap.is_empty wenv then t
  else
    match t.value with
    | OLAp (f, []) ->
      (match StringMap.find_opt f.string wenv with
       | Some ([], witness) -> witness
       | _ -> t)
    | OLAp (f, args) ->
      (match StringMap.find_opt f.string wenv with
       | Some (param_names, witness)
         when List.length param_names = List.length args ->
         let resolved_args = List.map (resolve_with_params wenv) args in
         let param_env =
           List.fold_left2 (fun acc p arg -> StringMap.add p arg acc)
             empty_env param_names resolved_args
         in
         resolve param_env witness
       | _ ->
         { t with value =
             OLAp (f, List.map (resolve_with_params wenv) args) })
    | _ -> t

(* === Type computation ============================================
   `compute_type` returns the OL type of a term in the current state.
   Used by `unify` for type-level propagation: when a meta is solved
   to some term, its recorded expected type is unified with the
   solving term's computed type. Returns None when the type can't
   be determined (e.g. for non-OL bindings, holes, or higher-order
   positions). *)
let compute_type (state : elab_state) (ctx : context) (t : ol) : ol option =
  let t = follow state.sols t in
  match t.value with
  | OLMeta id -> IntMap.find_opt id state.meta_types
  | OLHole -> None
  | OLAp (f, []) ->
    (match lookup_ctx ctx f.string with
     | FoundOL ([], ret) -> Some ret
     | _ -> None)
  | OLAp (f, args) ->
    (match lookup_ctx ctx f.string with
     | FoundOL (params, ret) when List.length params = List.length args ->
       let env =
         List.fold_left2 (fun acc (p_name, _) arg ->
           match p_name with
           | Some n -> StringMap.add n arg acc
           | None -> acc
         ) StringMap.empty params args
       in
       Some (resolve env ret)
     | _ -> None)

(* === Eager unification ===========================================
   When a meta is solved (`?A := term`), recursively unify the meta's
   recorded expected type with `compute_type state ctx term`. That
   transitive constraint is what lets a single concrete arg eventually
   solve multiple leading implicits at a constructor site.

   If the meta has an expected type but `compute_type` returns None
   (e.g. solving against a hole or a higher-order term), don't commit
   the solution — leave the meta open so it zonks to `?` rather than
   forcing a constraint we can't verify. *)
let rec unify (state : elab_state) (ctx : context) (a : ol) (b : ol)
    : elab_state option =
  let a = follow state.sols a in
  let b = follow state.sols b in
  let solve_meta state id term =
    if occurs state.sols id term then None
    else
      match IntMap.find_opt id state.meta_types,
            compute_type state ctx term with
      | Some expected_ty, Some actual_ty ->
        let state' = { state with sols = IntMap.add id term state.sols } in
        unify state' ctx expected_ty actual_ty
      | Some _, None ->
        (* Don't commit; meta stays open. *)
        Some state
      | None, _ ->
        Some { state with sols = IntMap.add id term state.sols }
  in
  match a.value, b.value with
  | OLHole, _ | _, OLHole -> Some state
  | OLMeta id1, OLMeta id2 when id1 = id2 -> Some state
  | OLMeta id1, OLMeta id2 ->
    (* Alias the higher-id meta to the lower one, then propagate the
       constraint via meta_types. *)
    let lo, hi = if id1 < id2 then (id1, id2) else (id2, id1) in
    let aliased = { value = OLMeta lo; meta = default_meta } in
    let state' = { state with sols = IntMap.add hi aliased state.sols } in
    (match IntMap.find_opt lo state.meta_types,
           IntMap.find_opt hi state.meta_types with
     | Some t1, Some t2 -> unify state' ctx t1 t2
     | _ -> Some state')
  | OLMeta id, _ -> solve_meta state id b
  | _, OLMeta id -> solve_meta state id a
  | OLAp (f1, args1), OLAp (f2, args2)
    when f1.string = f2.string
      && List.length args1 = List.length args2 ->
    List.fold_left2 (fun acc x y ->
      match acc with
      | None -> None
      | Some st -> unify st ctx x y
    ) (Some state) args1 args2
  | _ -> None

(* === Diagnostics ================================================= *)

type hole_info = {
  offset: int;
  context: context;
  goal: ol;
}

(* Inlay hint records — surface artifacts of elaboration that the
   editor renders as a small mark next to the head (`…` for implicit
   args, `°` for coercion wrappings) with the inferred OL subterm as
   the hover tooltip. *)
type inlay_hint = {
  hint_offset: int;            (* byte offset to anchor at *)
  hint_kind: ghost_kind;       (* Implicit or Coerce *)
  hint_tooltip: string;        (* hover text — rendered OL term(s) *)
}

type static_info = {
  errors: Error.t list;
  holes: hole_info list;
  inlay_hints: inlay_hint list;
  elaborated: ol option;
  bindings: context;
}

let empty_info : static_info = {
  errors = [];
  holes = [];
  inlay_hints = [];
  elaborated = None;
  bindings = empty_context;
}

let merge_info (a : static_info) (b : static_info) : static_info = {
  errors = a.errors @ b.errors;
  holes = a.holes @ b.holes;
  inlay_hints = a.inlay_hints @ b.inlay_hints;
  elaborated = b.elaborated;
  bindings = StringMap.union (fun _ _ v -> Some v) a.bindings b.bindings;
}

(* Walk an already-zonked elaborated term and emit both inlay hints
   AND "not fully solved" warnings, parameterised by a `strip`
   function (typically `strip_implicits`). Each ghost subtree carries
   its kind directly (Implicit / Coerce); there is no side table.

   • Maximal LEADING runs of Implicit-ghost args inside an Ap collapse
     to one `…` hint anchored at the head's end; if any ghost in the
     run is still unsolved we additionally emit a warning at the head.
   • A Coerce-ghost subtree contains exactly one non-ghost descendant
     (the user's coerced subject); we render `°` at the subject with
     the wrap (subject replaced by `□`) as the hint. *)
let extract_diagnostics
    (strip : ol -> ol)
    (sols : ol IntMap.t)
    (root : ol)
    : inlay_hint list * Error.t list =
  let hints = ref [] in
  let warns = ref [] in
  let rec contains_unsolved (t : ol) : bool =
    let t = follow sols t in
    match t.value with
    | OLMeta _ -> true
    | OLAp (_, args) -> List.exists contains_unsolved args
    | _ -> false
  in
  let rec find_subject (t : ol) : ol option =
    if not (is_ghost t.meta) then Some t
    else match t.value with
      | OLAp (_, args) ->
        List.fold_left (fun acc a ->
          match acc with
          | Some _ -> acc
          | None -> find_subject a
        ) None args
      | _ -> None
  in
  let box_ol : ol = {
    value = OLAp ({ string = box_char; meta = default_meta }, []);
    meta = default_meta;
  } in
  let rec substitute_box subj_start subj_end (t : ol) : ol =
    if t.meta.start = subj_start
       && t.meta.end_ = subj_end
       && not (is_ghost t.meta)
    then box_ol
    else match t.value with
      | OLAp (f, args) ->
        { t with value =
            OLAp (f, List.map (substitute_box subj_start subj_end) args) }
      | _ -> t
  in
  let render_args subs =
    subs
    |> List.map (fun g -> Print.print_ol (strip (zonk sols g)))
    |> String.concat " "
  in
  let rec walk (t : ol) : unit =
    match t.meta.ghost with
    | Some Coerce ->
      (match find_subject t with
       | None -> ()
       | Some subj ->
         let tooltip_term =
           substitute_box subj.meta.start subj.meta.end_ t
         in
         let tooltip = Print.print_ol (strip (zonk sols tooltip_term)) in
         hints := !hints @ [{
           hint_offset = subj.meta.start;
           hint_kind = Coerce;
           hint_tooltip = tooltip;
         }];
         if contains_unsolved t then
           warns := !warns @ [Error.warn
             "Coercion not fully solved" subj.meta.start subj.meta.end_];
         walk subj)
    | _ ->
      (match t.value with
       | OLAp (f, args) ->
         let rec split_leading acc = function
           | (a : ol) :: rest when a.meta.ghost = Some Implicit ->
             split_leading (a :: acc) rest
           | xs -> (List.rev acc, xs)
         in
         let (lead, rest) = split_leading [] args in
         if lead <> [] then begin
           hints := !hints @ [{
             hint_offset = f.meta.end_;
             hint_kind = Implicit;
             hint_tooltip = render_args lead;
           }];
           if List.exists contains_unsolved lead then
             warns := !warns @ [Error.warn
               "Implicit arguments not fully solved"
               f.meta.start f.meta.end_]
         end;
         List.iter walk rest
       | _ -> ())
  in
  walk root;
  (!hints, !warns)

(* Resolve each hole's goal through the strip-and-zonk pipeline so
   per-decl meta IDs don't leak into hole_info, and so the goal is
   rendered in its compactest form. *)
let resolve_hole_goals
    (strip : ol -> ol)
    (sols : ol IntMap.t)
    (holes : hole_info list)
    : hole_info list =
  List.map (fun h -> { h with goal = strip (zonk sols h.goal) }) holes

(* Shadowing diagnostic. Returns a warning if `name` already exists in
   `ctx` with a different source position. *)
let shadow_check (name : string) (name_meta : meta) (ctx : context)
    : Error.t list =
  match StringMap.find_opt name ctx with
  | None -> []
  | Some (OLBinding _) ->
    (* For the slice we don't carry def-site positions, so any
       reoccurrence is a shadow. Pre-binding the decl's own name for
       self-reference fires this; the caller filters that case. *)
    [Error.warn "Shadows existing binding" name_meta.start name_meta.end_]

(* === OL term elaboration ========================================= *)

let rec check_ol_term
    (state : elab_state)
    (ctx : context)
    (expected : ol option)
    (t : ol)
    : static_info * elab_state =
  match t.value with
  | OLHole ->
    (* A user `?` and an elaborator-inserted meta are the same concept:
       a unification variable. Allocate a fresh meta carrying the
       expected type so type-level propagation can constrain it; the
       source position is also registered as a hole for the IDE. *)
    let expected_ty = match expected with Some e -> e | None -> mk_ol OLHole in
    let (m, state') = mk_meta state expected_ty t.meta in
    let info = {
      empty_info with
      elaborated = Some m;
      holes = [{ offset = t.meta.start; context = ctx; goal = expected_ty }];
    } in
    (info, state')

  | OLMeta id ->
    (* Already-elaborated meta. Look up its recorded expected type, then
       subsume against the caller-supplied expected (so chained metas
       transitively propagate). *)
    let inferred = match IntMap.find_opt id state.meta_types with
      | Some ty -> ty
      | None -> mk_ol OLHole
    in
    let (errs, state') = match expected with
      | None -> ([], state)
      | Some e ->
        (match unify state ctx e inferred with
         | Some s -> ([], s)
         | None ->
           let msg =
             "Inconsistency (expected "
             ^ Print.print_ol (zonk state.sols e)
             ^ ", found "
             ^ Print.print_ol (zonk state.sols inferred)
             ^ ")"
           in
           ([Error.mark msg t.meta.start t.meta.end_], state))
    in
    ({ empty_info with errors = errs; elaborated = Some t }, state')

  | OLAp (f, args) ->
    (match lookup_ctx ctx f.string with
     | NotFound ->
       let err = Error.mark
         ("Unbound identifier " ^ f.string) f.meta.start f.meta.end_ in
       ({ empty_info with errors = [err]; elaborated = Some t }, state)

     | FoundOL (params, ret) ->
       let n_params = List.length params in
       let n_args = List.length args in
       (* Too-many-args is a hard error but doesn't stop elaboration:
          we still walk all the slots so the elaborated form preserves
          what the user wrote (idempotence). *)
       let hard_arity_errs =
         if n_args > n_params then
           [Error.mark "Too many arguments" f.meta.start f.meta.end_]
         else []
       in
       let n_missing = max 0 (n_params - n_args) in
       let total_slots = n_missing + n_args in
       (* Slot-by-slot walk. Slot i is:
          • overflow (i >= n_params) — user over-applied; check at olHole.
          • ghost   (i < n_missing) — leading auto-inserted implicit.
          • user    (otherwise)     — user-supplied arg at i - n_missing.
          Each non-overflow slot has its expected_ty resolved through
          the prior-elaborated env, so dependent param types work. *)
       let (info, final_state, final_env, elab_args) =
         List.fold_left (fun (acc_info, acc_st, acc_env, acc_args) i ->
           let is_overflow = i >= n_params in
           let is_ghost = i < n_missing in
           let expected_ty =
             if is_overflow then mk_ol OLHole
             else
               let (_, p_ty) = List.nth params i in
               resolve acc_env p_ty
           in
           let (arg, arg_info, new_st) =
             if is_ghost then
               let (g, ns) = mk_ghost_meta Implicit acc_st expected_ty t.meta in
               (g, empty_info, ns)
             else
               let user_arg = List.nth args (i - n_missing) in
               let (info, ns) =
                 check_ol_term acc_st ctx (Some expected_ty) user_arg
               in
               (user_arg, info, ns)
           in
           let elab_arg = match arg_info.elaborated with
             | Some e -> e
             | None -> arg
           in
           let env' =
             if is_overflow then acc_env
             else
               let (p_name, _) = List.nth params i in
               match p_name with
               | Some n -> StringMap.add n elab_arg acc_env
               | None -> acc_env
           in
           (merge_info acc_info arg_info, new_st, env',
            acc_args @ [elab_arg])
         ) (empty_info, state, empty_env, [])
           (List.init total_slots (fun i -> i))
       in
       let elaborated = { t with value = OLAp (f, elab_args) } in
       let inferred = resolve final_env ret in
       (* Subsume against the outer expected via unification. *)
       let (sub_errs, final_state') = match expected with
         | None -> ([], final_state)
         | Some e ->
           (match unify final_state ctx e inferred with
            | Some s -> ([], s)
            | None ->
              let msg =
                "Inconsistency (expected "
                ^ Print.print_ol (zonk final_state.sols e)
                ^ ", found "
                ^ Print.print_ol (zonk final_state.sols inferred)
                ^ ")"
              in
              ([Error.mark msg t.meta.start t.meta.end_], final_state))
       in
       let info' = {
         info with
         errors = info.errors @ hard_arity_errs @ sub_errs;
         elaborated = Some elaborated;
       } in
       (info', final_state'))

(* Compact rendering of an elaborated term for inlay hints / hole
   goals. For each OLAp, try successively stripping leading args and
   re-elaborating the result; if the elaborator can re-derive an
   equal term, keep the stripped form. The `□` (box) character marks
   the coerce-subject slot; treated as a wildcard during the equality
   check. *)
and strip_implicits (sols : ol IntMap.t) (ctx : context) (t : ol) : ol =
  let rec equal_for_strip (a : ol) (b : ol) : bool =
    match a.value, b.value with
    | OLAp ({ string = s; _ }, []), _ when s = box_char -> true
    | _, OLAp ({ string = s; _ }, []) when s = box_char -> true
    | OLMeta _, OLMeta _ -> true
    | OLHole, OLHole -> true
    | OLAp (f1, as1), OLAp (f2, as2) ->
      f1.string = f2.string
      && List.length as1 = List.length as2
      && List.for_all2 equal_for_strip as1 as2
    | _ -> false
  in
  let rec replace_box_with_hole (t : ol) : ol =
    match t.value with
    | OLAp ({ string = s; _ }, []) when s = box_char ->
      { t with value = OLHole }
    | OLAp (f, args) ->
      { t with value = OLAp (f, List.map replace_box_with_hole args) }
    | _ -> t
  in
  let rec strip (t : ol) : ol =
    match t.value with
    | OLAp (f, args) ->
      let target = zonk sols t in
      let n = List.length args in
      let try_strip (k : int) : ol list option =
        let kept = List.filteri (fun i _ -> i >= k) args in
        let stripped : ol = { t with value = OLAp (f, kept) } in
        let strip_check = replace_box_with_hole stripped in
        let (info, state) =
          check_ol_term empty_elab_state ctx None strip_check
        in
        if info.errors <> [] then None
        else
          match info.elaborated with
          | None -> None
          | Some elab ->
            let elab_zonked = zonk state.sols elab in
            if equal_for_strip target elab_zonked then Some kept
            else None
      in
      let rec find_max_strip k current_kept =
        if k > n then current_kept
        else
          match try_strip k with
          | Some kept -> find_max_strip (k + 1) kept
          | None -> current_kept
      in
      let stripped_args = find_max_strip 1 args in
      let recursed = List.map strip stripped_args in
      { t with value = OLAp (f, recursed) }
    | _ -> t
  in
  strip t

(* === Decl / line / block walks =================================== *)

(* Elaborate a declaration line. Each arg's type is checked in a context
   already extended by prior args (dependent types). The return type is
   checked in the context with all args bound.

   Each decl is elaborated against a FRESH `empty_elab_state` — per main's
   typeDeclaration rule, meta IDs are decl-local. The external binding
   we store in the surrounding context is zonked through the local
   solutions and any unsolved meta is replaced by `OLHole` (which acts
   as a wildcard under unification), so per-decl meta IDs never leak.

   Two contexts come in (see `check_block`):
   • `elab_ctx` — the WHOLE block is in scope. Earlier decls appear as
     their elaborated bindings; this decl itself and later decls appear
     as their preliminary (un-elaborated, as-written) bindings. Type
     resolution (arg / ret elaboration) reads this, so a decl may refer
     to any peer in its block, including itself (the bootstrap pattern
     `Sort : Sort`) and forward peers.
   • `outer_ctx` — base context plus only the ELABORATED earlier decls
     (no self, no forward peers). This matches the left-to-right context
     the old code carried, and is used for shadow warnings + the
     completeness-ref dependency walk, so neither self nor a forward
     peer is mistaken for a shadow or an external dependency. *)
let check_decl_line ~(elab_ctx : context) ~(outer_ctx : context)
    (d : decl_line) : static_info * full_type =
  let state = empty_elab_state in
  let preliminary_params =
    List.map (fun (a : decl_arg) ->
      (Some a.decl_arg_name.string, a.decl_arg_type)
    ) d.args
  in
  let preliminary_ft : full_type = (preliminary_params, d.ret_type) in
  let self_shadow_warns =
    shadow_check d.decl_name.string d.decl_name.meta outer_ctx
  in
  (* Shadow checks for params run against a prefix-only context (outer +
     self + prior args), NOT `elab_ctx`, so a param sharing a name with a
     forward sibling decl isn't spuriously flagged. *)
  let shadow_base =
    StringMap.add d.decl_name.string (OLBinding preliminary_ft) outer_ctx
  in
  let (arg_info, state_after_args, ctx_with_args, _shadow_with_args, param_spec) =
    List.fold_left
      (fun (acc_info, acc_st, acc_ctx, acc_shadow, acc_params) (a : decl_arg) ->
      let (info, st') = check_ol_term acc_st acc_ctx None a.decl_arg_type in
      let elaborated_ty = match info.elaborated with Some e -> e | None -> a.decl_arg_type in
      let name = a.decl_arg_name.string in
      let param_shadow_warns =
        shadow_check name a.decl_arg_name.meta acc_shadow
      in
      let info = { info with errors = info.errors @ param_shadow_warns } in
      let binding_ty : full_type = ([], elaborated_ty) in
      let ctx' = StringMap.add name (OLBinding binding_ty) acc_ctx in
      let shadow' = StringMap.add name (OLBinding binding_ty) acc_shadow in
      (merge_info acc_info info, st', ctx', shadow',
       acc_params @ [(Some name, elaborated_ty)])
    ) (empty_info, state, elab_ctx, shadow_base, []) d.args
  in
  let (ret_info, state_after_ret) =
    check_ol_term state_after_args ctx_with_args None d.ret_type in
  let elab_ret = match ret_info.elaborated with Some e -> e | None -> d.ret_type in
  let sols = state_after_ret.sols in
  let strip = strip_implicits sols ctx_with_args in
  (* Hint + warning extraction runs against the pre-zonk elaborated
     terms so ghost markers + per-decl meta IDs are still in scope.
     `strip` compacts each tooltip by stripping leading args the
     elaborator can re-infer. *)
  let (hints, warns) =
    let pairs = List.map snd param_spec @ [elab_ret] in
    List.fold_left (fun (hs, ws) t ->
      let (h, w) = extract_diagnostics strip sols t in
      (hs @ h, ws @ w)
    ) ([], []) pairs
  in
  (* Build the external binding: zonk every elaborated piece through the
     local solutions; replace surviving metas with OLHole. *)
  let external_params =
    List.map (fun (n, ty) -> (n, zonk_and_forget sols ty)) param_spec
  in
  let external_ret = zonk_and_forget sols elab_ret in
  let external_ft : full_type = (external_params, external_ret) in
  let resolved_holes =
    resolve_hole_goals strip sols (arg_info.holes @ ret_info.holes)
  in
  (* Per-decl completeness: no holes, no real errors, all external
     refs themselves complete. Refs are collected against `outer_ctx`
     (no self, no forward peers) so a self- or forward-reference isn't
     counted as an external dependency. Marked tentatively here. *)
  let local_errs = arg_info.errors @ ret_info.errors in
  let type_has_holes =
    ol_has_holes external_ret
    || List.exists (fun (_, ty) -> ol_has_holes ty) external_params
  in
  let type_refs =
    List.concat (
      List.map (fun (_, ty) -> ol_collect_refs ty outer_ctx) external_params)
    @ ol_collect_refs external_ret outer_ctx
  in
  let local_complete =
    not type_has_holes
    && not (Error.has_real local_errs)
    && all_refs_complete type_refs
  in
  Hashtbl.replace completeness_ref d.decl_name.string local_complete;
  let info = {
    errors = self_shadow_warns @ local_errs @ warns;
    holes = resolved_holes;
    inlay_hints = hints;
    elaborated = None;
    bindings = StringMap.singleton d.decl_name.string (OLBinding external_ft);
  } in
  (info, external_ft)

(* Check a whole block with circular (mutual) declaration dependence.

   The entire block is in scope while checking each declaration: we seed
   a context with every decl's PRELIMINARY (as-written) binding, then walk
   the decls in order, replacing each one's preliminary binding with its
   elaborated binding as we go. So declaration [i] is checked against the
   elaborated forms of [0..i-1] and the preliminary forms of [i..end]
   (its own included, for self-reference).

   `outer_ctx` tracks only the base context plus the ELABORATED earlier
   decls — the left-to-right context the old code carried — and is handed
   to `check_decl_line` for shadow / completeness checks. Its final value
   (base + all elaborated decls) is what we return for the next block. *)
let check_block (ctx : context) (b : block) : static_info * context =
  let lines = match b with
    | Postulate pb -> pb.postulate_lines
    | Construct cb -> cb.construct_lines
    | MetaBlock _ -> []
  in
  match b with
  | MetaBlock _ -> (empty_info, ctx)
  | Postulate _ | Construct _ ->
    let decls =
      List.filter_map (function Decl d -> Some d | Tag _ -> None) lines
    in
    let prelim_of (d : decl_line) : full_type =
      let params =
        List.map (fun (a : decl_arg) ->
          (Some a.decl_arg_name.string, a.decl_arg_type)
        ) d.args
      in
      (params, d.ret_type)
    in
    (* Whole block seeded as preliminary bindings on top of the base. *)
    let block_ctx0 =
      List.fold_left (fun acc (d : decl_line) ->
        StringMap.add d.decl_name.string (OLBinding (prelim_of d)) acc
      ) ctx decls
    in
    let (info, _elab_ctx, outer_ctx) =
      List.fold_left (fun (acc_info, elab_ctx, outer_ctx) line ->
        match line with
        | Tag _ -> (acc_info, elab_ctx, outer_ctx)
        | Decl d ->
          let (li, elab_ft) = check_decl_line ~elab_ctx ~outer_ctx d in
          let name = d.decl_name.string in
          (* Swap this decl's preliminary binding for its elaborated one
             in both contexts before moving to the next decl. *)
          let elab_ctx' = StringMap.add name (OLBinding elab_ft) elab_ctx in
          let outer_ctx' = StringMap.add name (OLBinding elab_ft) outer_ctx in
          (merge_info acc_info li, elab_ctx', outer_ctx')
      ) (empty_info, block_ctx0, ctx) lines
    in
    (info, outer_ctx)

let check_program (prog : program) : static_info =
  reset_completeness ();
  let (info, _final_ctx) =
    List.fold_left (fun (acc_info, acc_ctx) b ->
      let (info, ctx') = check_block acc_ctx b in
      (merge_info acc_info info, ctx')
    ) (empty_info, initial_context) prog
  in
  info
