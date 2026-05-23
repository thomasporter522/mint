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

(* === Context lookup ============================================== *)

type lookup_result =
  | NotFound
  | FoundOL of full_type

let lookup_ctx (ctx : context) (name : string) : lookup_result =
  match StringMap.find_opt name ctx with
  | None -> NotFound
  | Some (OLBinding ft) -> FoundOL ft

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

(* Walk an elaborated OL term; for every OLAp, collapse the leading
   run of ghost-marked args into a single inlay hint anchored at the
   head's end. Trailing or mid-spine ghosts (currently never produced
   by the elaborator, but possible in principle) would need a
   different anchor strategy; we ignore them for now. *)
let rec extract_hints (sols : ol IntMap.t) (t : ol) : inlay_hint list =
  match t.value with
  | OLAp (f, args) ->
    let recursive = List.concat_map (extract_hints sols) args in
    let ghost_args =
      let rec take_leading acc = function
        | [] -> List.rev acc
        | (a : ol) :: rest when is_ghost a.meta -> take_leading (a :: acc) rest
        | _ :: _ -> List.rev acc
      in
      take_leading [] args
    in
    let new_hints =
      if ghost_args = [] then []
      else
        let anchor = f.meta.end_ in
        let by_kind kind =
          List.filter_map (fun (g : ol) ->
            match g.meta.ghost with
            | Some k when k = kind -> Some g
            | _ -> None
          ) ghost_args
        in
        let mk kind subs =
          if subs = [] then []
          else
            let tooltip =
              subs
              |> List.map (fun g -> Print.print_ol (follow sols g))
              |> String.concat ", "
            in
            [{ hint_offset = anchor; hint_kind = kind; hint_tooltip = tooltip }]
        in
        mk Implicit (by_kind Implicit) @ mk Coerce (by_kind Coerce)
    in
    recursive @ new_hints
  | _ -> []

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
           ([Error.mark "Type mismatch on metavariable" t.meta.start t.meta.end_], state))
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
              let err = Error.mark
                ("Type mismatch on " ^ f.string)
                t.meta.start t.meta.end_
              in
              ([err], final_state))
       in
       let info' = {
         info with
         errors = info.errors @ hard_arity_errs @ sub_errs;
         elaborated = Some elaborated;
       } in
       (info', final_state'))

(* === Decl / line / block walks =================================== *)

(* Elaborate a declaration line. Each arg's type is checked in a context
   already extended by prior args (dependent types). The return type is
   checked in the context with all args bound.

   Each decl is elaborated against a FRESH `empty_elab_state` — per main's
   typeDeclaration rule, meta IDs are decl-local. The external binding
   we store in the surrounding context is zonked through the local
   solutions and any unsolved meta is replaced by `OLHole` (which acts
   as a wildcard under unification), so per-decl meta IDs never leak.

   Self-reference: the name being defined is pre-bound (using its un-
   elaborated written types) before its own arg/ret types are checked.
   That lets the bootstrap pattern `Sort : Sort` elaborate — the second
   `Sort` resolves to the pre-binding. *)
let check_decl_line (ctx : context) (d : decl_line)
    : static_info * context =
  let state = empty_elab_state in
  let preliminary_params =
    List.map (fun (a : decl_arg) ->
      (Some a.decl_arg_name.string, a.decl_arg_type)
    ) d.args
  in
  let preliminary_ft : full_type = (preliminary_params, d.ret_type) in
  let ctx_with_self =
    StringMap.add d.decl_name.string (OLBinding preliminary_ft) ctx
  in
  let (arg_info, state_after_args, ctx_with_args, param_spec) =
    List.fold_left (fun (acc_info, acc_st, acc_ctx, acc_params) (a : decl_arg) ->
      let (info, st') = check_ol_term acc_st acc_ctx None a.decl_arg_type in
      let elaborated_ty = match info.elaborated with Some e -> e | None -> a.decl_arg_type in
      let name = a.decl_arg_name.string in
      let binding_ty : full_type = ([], elaborated_ty) in
      let ctx' = StringMap.add name (OLBinding binding_ty) acc_ctx in
      (merge_info acc_info info, st', ctx', acc_params @ [(Some name, elaborated_ty)])
    ) (empty_info, state, ctx_with_self, []) d.args
  in
  let (ret_info, state_after_ret) =
    check_ol_term state_after_args ctx_with_args None d.ret_type in
  let elab_ret = match ret_info.elaborated with Some e -> e | None -> d.ret_type in
  let sols = state_after_ret.sols in
  (* Inlay-hint extraction runs against the pre-zonk elaborated terms,
     so ghost markers + per-decl meta IDs are still in scope and can
     be resolved against `sols`. *)
  let hints =
    let walked =
      List.concat_map (fun (_, ty) -> extract_hints sols ty) param_spec
    in
    walked @ extract_hints sols elab_ret
  in
  (* Build the external binding: zonk every elaborated piece through the
     local solutions; replace surviving metas with OLHole. *)
  let external_params =
    List.map (fun (n, ty) -> (n, zonk_and_forget sols ty)) param_spec
  in
  let external_ret = zonk_and_forget sols elab_ret in
  let external_ft : full_type = (external_params, external_ret) in
  let ctx' = StringMap.add d.decl_name.string (OLBinding external_ft) ctx in
  (* Resolve hole goals through the same zonk so per-decl meta IDs don't
     leak into hole_info either. *)
  let resolved_holes =
    List.map (fun h -> { h with goal = zonk_and_forget sols h.goal })
      (arg_info.holes @ ret_info.holes)
  in
  let info = {
    errors = arg_info.errors @ ret_info.errors;
    holes = resolved_holes;
    inlay_hints = hints;
    elaborated = None;
    bindings = StringMap.singleton d.decl_name.string (OLBinding external_ft);
  } in
  (info, ctx')

let check_ol_line (ctx : context) (l : ol_line) : static_info * context =
  match l with
  | Decl d -> check_decl_line ctx d
  | Tag _ -> (empty_info, ctx)

let check_block (ctx : context) (b : block) : static_info * context =
  match b with
  | Postulate pb ->
    List.fold_left (fun (info, ctx') line ->
      let (li, ctx'') = check_ol_line ctx' line in
      (merge_info info li, ctx'')
    ) (empty_info, ctx) pb.postulate_lines

  | Construct cb ->
    List.fold_left (fun (info, ctx') line ->
      let (li, ctx'') = check_ol_line ctx' line in
      (merge_info info li, ctx'')
    ) (empty_info, ctx) cb.construct_lines

  | MetaBlock _ -> (empty_info, ctx)

let check_program (prog : program) : static_info =
  let (info, _final_ctx) =
    List.fold_left (fun (acc_info, acc_ctx) b ->
      let (info, ctx') = check_block acc_ctx b in
      (merge_info acc_info info, ctx')
    ) (empty_info, initial_context) prog
  in
  info
