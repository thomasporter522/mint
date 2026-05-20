postulate
sort : sort
U : U
-- function types
to (A B : U) : U
ap (A B : U) (f : to A B) (a : A) : B
pi (A : U) (B : to A U) : U
dap (A : U) (B : to A U) (f : pi A B) (a : A) : ap B a
-- equations
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
-- todo: use a unified eq eliminator
cast (A B : U) : to (eq A B) (to A B)
sym (A B : U) (a : A) (b : B) : to (eq a b) (eq b a)
trans (A B C : U) (a : A) (b : B) (c : C) : to (eq a b) (to (eq b c) (eq a c))

meta 
newtag #reduction

postulate 
cast-eq (A B : U) (e : eq A B) (a : A) : eq (ap (ap cast e) a) a
#reduction cast-eq 

postulate
cong-ap (A B : U)
  (f : to A B) (g : to A B)
  (a : A) (b : A) 
  : to (eq f g) 
    (to (eq a b) 
      (eq (ap f a) (ap g b)))
cong-to (A1 B1 A2 B2 : U)
  (eA : eq A1 A2) (eB : eq B1 B2)
  : eq (to A1 B1) (to A2 B2)

abs-const (X A : U)
  : to A (to X A)
abs-const-eq (X A : U)
  (x : X) (a : A)
  : eq (ap (ap (abs-const) a) x) a
#reduction abs-const-eq
abs-ident (X : U)
  : to X X
abs-ident-eq (X : U) 
  (x : X)
  : eq (ap (abs-ident) x) x
#reduction abs-ident-eq
abs-ap (X A B : U) 
  : to (to X (to A B)) (to (to X A) (to X B))
abs-ap-eq (X A B : U) 
  (f : to X (to A B)) 
  (a : to X A) 
  (x : X) 
  : eq (ap (ap (ap (abs-ap) f) a) x) (ap (ap f x) (ap a x))
#reduction abs-ap-eq
abs-to (X : U)
  : to (to X U) (to (to X U) (to X U))
abs-to-eq (X : U) (A : to X U) (B : to X U) 
  (x : X) 
  : eq (ap (ap (ap (abs-to) A) B) x) (to (ap A x) (ap B x))
#reduction abs-to-eq
abs-eq (X : U)
  : to (to X U) (to (to X U) (to X U))
abs-eq-eq (X : U) (A : to X U) (B : to X U) 
  (x : X) 
  : eq (ap (ap (ap (abs-eq) A) B) x) (eq (ap A x) (ap B x))
#reduction abs-eq-eq

meta
    -- True iff this binding's tag list carries #reduction.
    has-reduction : ((List Tag) -> Bool) = fun tags =>
      (foldl (fun acc => fun t => acc || (t == #reduction)) false tags)
    -- List membership by ==.
    member : (Term -> ((List Term) -> Bool)) = fun x => fun xs =>
      (foldl (fun acc => fun e => acc || (e == x)) false xs)
    -- Assoc-list lookup.
    lookup : (Term -> ((List (Term, Term)) -> (Result Term))) = fun k => fun xs =>
      (foldl (fun acc => fun pair =>
        match acc with
        | Ok _ => acc
        | Error _ =>
          match pair with
          | (key, val) => if (key == k) then (Ok val) else acc end
          end
        end
      ) (Error "not found") xs)
    -- Reverse a list of terms.
    reverse-terms : ((List Term) -> (List Term)) = fun xs =>
      (foldl (fun acc => fun x => x :: acc) [] xs)
    -- Names from a list of (name, type) param tuples.
    param-names : ((List (Term, Term)) -> (List Term)) = fun params =>
      (foldl (fun acc => fun p =>
        match p with
        | (n, _) => (append acc [n])
        end
      ) [] params)
    -- For each binder, retrieve its bound value (or ? if unbound).
    fill-args : ((List Term) -> ((List (Term, Term)) -> (List Term))) = fun binders => fun bindings =>
      (foldl (fun acc => fun b =>
        match (lookup b bindings) with
        | Ok v => (append acc [v])
        | Error _ => (append acc [?])
        end
      ) [] binders)
    -- Match a pattern term against a target. Identifiers listed in
    -- `binders` bind to subterms (with consistency checks on repeats);
    -- other identifiers must match literally. Ap recurses, aligning args
    -- at the END so the target may carry leading implicit type args
    -- that the pattern elides.
    match-term : ((List Term) -> ((List (Term, Term)) -> (Term -> (Term -> (Result (List (Term, Term))))))) =
      fun binders => fun bindings => fun pat => fun term =>
        let pp = (decompose pat) in
        let ph = (fst pp) in
        let pa = (snd pp) in
        match pa with
        | [] =>
          if (member ph binders) then
            match (lookup ph bindings) with
            | Ok existing =>
              if (existing == term) then (Ok bindings) else (Error "binder conflict") end
            | Error _ => (Ok (append bindings [(ph, term)]))
            end
          else
            if (pat == term) then (Ok bindings) else (Error "atom mismatch") end
          end
        | _ :: _ =>
          let tp = (decompose term) in
          let th = (fst tp) in
          let ta = (snd tp) in
          match ta with
          | [] => (Error "expected ap, got atom")
          | _ :: _ =>
            match (match-term binders bindings ph th) with
            | Ok b1 => (align-match binders b1 (reverse-terms pa) (reverse-terms ta))
            | Error msg => (Error msg)
            end
          end
        end
    -- Walk reversed pattern/target arg lists in parallel. Pattern empty
    -- = success (any leading target args are skipped implicits). Target
    -- empty with pattern non-empty = failure.
    align-match : ((List Term) -> ((List (Term, Term)) -> ((List Term) -> ((List Term) -> (Result (List (Term, Term))))))) =
      fun binders => fun bindings => fun rps => fun rts =>
        match rps with
        | [] => (Ok bindings)
        | p :: ps =>
          match rts with
          | [] => (Error "pattern wider than term")
          | t :: ts =>
            match (match-term binders bindings p t) with
            | Ok b1 => (align-match binders b1 ps ts)
            | Error msg => (Error msg)
            end
          end
        end
    -- Substitute bindings into a term: binder identifiers get replaced
    -- by their bound values; everything else recurses structurally.
    subst-list : ((List (Term, Term)) -> ((List Term) -> (List Term))) = fun bindings => fun ts =>
      (foldl (fun acc => fun t => (append acc [(subst bindings t)])) [] ts)
    subst : ((List (Term, Term)) -> (Term -> Term)) = fun bindings => fun t =>
      let p = (decompose t) in
      let h = (fst p) in
      let args = (snd p) in
      match args with
      | [] =>
        match (lookup h bindings) with
        | Ok v => v
        | Error _ => t
        end
      | _ :: _ =>
        (apply (subst bindings h) (subst-list bindings args))
      end
    -- Try one context entry as a rewrite rule. Recognises retTypes
    -- shaped `eq A B LHS RHS` (the equational form); matches the target
    -- against LHS, substitutes the bindings into RHS, and builds the
    -- proof as `(rule-name binder1 binder2 …)`.
    try-rule : ((Term, (List (Term, Term)), Term, (List Tag)) -> (Term -> (Result (Term, Term)))) =
      fun sig => fun term =>
        match sig with
        | (name, params, retType, _) =>
          let binders = (param-names params) in
          let rp = (decompose retType) in
          let rh = (fst rp) in
          let ra = (snd rp) in
          if (rh == eq) then
            match ra with
            | [_, _, lhs, rhs] =>
              match (match-term binders [] lhs term) with
              | Ok bindings =>
                let reduced = (subst bindings rhs) in
                let proof = (apply name (fill-args binders bindings)) in
                (Ok (reduced, proof))
              | Error msg => (Error msg)
              end
            | _ => (Error "retType is not 4-arg eq")
            end
          else (Error "retType head is not eq") end
        end
    -- Iterate context's #reduction-tagged entries, returning the first
    -- one that fires on `term`. Generic — no knowledge of any specific
    -- rule's identity.
    try-top : ((List Signature) -> (Term -> (Result (Term, Term)))) = fun ctx => fun term =>
      (foldl (fun acc => fun entry =>
        match acc with
        | Ok _ => acc
        | Error _ =>
          match entry with
          | (_, _, _, tags) =>
            if (has-reduction tags) then (try-rule entry term) else acc end
          end
        end
      ) (Error "no rule fired") ctx)
    -- Recursive beta-reducer. Structural recursion uses cong-ap for the
    -- ap application primitive and cong-to for the to function-type
    -- former; everything else refls out. After subterms settle, try a
    -- rule at the top and recurse on its rhs. Returns
    -- (normal-form, eq term normal-form).
    beta-reduce : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun term =>
      let sub = match term with
        | (ap A B f a) =>
          let fr = (beta-reduce ctx f) in
          let ar = (beta-reduce ctx a) in
          ((ap A B (fst fr) (fst ar)), (ap (ap cong-ap (snd fr)) (snd ar)))
        | (to A B) =>
          let ar = (beta-reduce ctx A) in
          let br = (beta-reduce ctx B) in
          ((to (fst ar) (fst br)), (cong-to (snd ar) (snd br)))
        | _ => (term, (refl ? term))
        end in
      let st = (fst sub) in
      let sp = (snd sub) in
      match (try-top ctx st) with
      | Ok step =>
        let next-term = (fst step) in
        let step-proof = (snd step) in
        let rec = (beta-reduce ctx next-term) in
        let final = (fst rec) in
        let final-proof = (snd rec) in
        let chain1 = (ap (ap trans sp) step-proof) in
        (final, (ap (ap trans chain1) final-proof))
      | Error _ => (st, sp)
      end
    -- Structural consistency: like ==, but a hole on either side is
    -- compatible with anything. Lets us bail on coerce candidates whose
    -- normal forms clash at a concrete head (the trans/cast wrap would
    -- be ill-typed and cascade into nested coerce attempts during
    -- verify) while still admitting cases where the heads agree modulo
    -- metas the kernel will solve via unification.
    consistent : (Term -> (Term -> Bool)) = fun a => fun b =>
      let pa = (decompose a) in
      let pb = (decompose b) in
      let ha = (fst pa) in
      let hb = (fst pb) in
      if (ha == ?) then true else
      if (hb == ?) then true else
      if (ha == hb) then (consistent-list (snd pa) (snd pb))
      else false end end end
    consistent-list : ((List Term) -> ((List Term) -> Bool)) = fun xs => fun ys =>
      match xs with
      | [] =>
        match ys with
        | [] => true
        | _ :: _ => false
        end
      | x :: xt =>
        match ys with
        | [] => false
        | y :: yt =>
          if (consistent x y) then (consistent-list xt yt) else false end
        end
      end
    -- Reduce both sides to (hopefully shared) normal forms; chain
    -- `eq found nf` with `sym (eq expected nf)` to get `eq found
    -- expected`; wrap in cast. Gated on `consistent` so a guaranteed
    -- structural clash bails immediately; admissible cases proceed and
    -- the kernel's verify pass runs unification on the wrap.
    coerce beta = fun ctx => fun expected => fun found => fun contents =>
      let fr = (beta-reduce ctx found) in
      let er = (beta-reduce ctx expected) in
      if (consistent (fst fr) (fst er)) then
        let full = (ap (ap trans (snd fr)) (ap sym (snd er))) in
        (Ok (ap (ap cast full) contents))
      else (Error "beta normal forms inconsistent") end

meta
  schema void-schema = 
    fun ctx => fun s => 
      (Ok [(pi U (abs-ident)), abs-ident])

construct by void-schema
void : U
void-rec : to void (pi U (abs-ident))meta 
  schema unit-schema =
        fun ctx => fun s =>
          match s with
          | [_, (_,_,_,_), _, _] =>
          (Ok [
            (pi U (ap (ap abs-to abs-ident) abs-ident)),
            ?,
            ?,
            ?
            ])
          | _ => (Error "invalid")
          end
construct by unit-schema
unit : U
unit-star : unit
unit-rec : pi (ap (ap abs-to (ap abs-const unit)) (ap (ap abs-to abs-ident) abs-ident))
unit-rec-eq (M : U) (star-case : M) : 
  eq M M (ap (ap 
    (dap unit-rec M)
     unit-star) star-case) star-case