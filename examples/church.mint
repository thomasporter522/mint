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
    schema void-schema = 
        fun ctx => fun s => 
          (Ok [(pi U (abs-ident)), abs-ident])
construct by void-schema
void : U
void-rec : to void (pi U (abs-ident))
meta
    -- Tag membership: does this binding's tag list carry #reduction?
    has-reduction : ((List Tag) -> Bool) = fun tags =>
      (foldl (fun acc => fun t => acc || (t == #reduction)) false tags)
    -- Is a specific OL name available in ctx AND tagged #reduction?
    rule-enabled : (Term -> ((List Signature) -> Bool)) = fun name => fun ctx =>
      (foldl (fun acc => fun entry =>
        if acc then acc else
        match entry with
        | (n, _, _, tags) =>
          if (n == name) then (has-reduction tags) else false end
        end
        end
      ) false ctx)
    -- Single-rule trials. Each matches the rule's specific outer shape;
    -- on match, returns (rhs-with-substitution, rule-applied-proof).
    -- The proof is `(name X… vals…)` with metas for type-args.
    try-ident : (Term -> (Result (Term, Term))) = fun term =>
      match term with
      | (ap _ _ (abs-ident _) x) =>
        (Ok (x, (abs-ident-eq ? x)))
      | _ => (Error "no")
      end
    try-const : (Term -> (Result (Term, Term))) = fun term =>
      match term with
      | (ap _ _ (ap _ _ (abs-const _ _) ia) oa) =>
        (Ok (ia, (abs-const-eq ? ? oa ia)))
      | _ => (Error "no")
      end
    try-apf : (Term -> (Result (Term, Term))) = fun term =>
      match term with
      | (ap _ _ (ap _ _ (ap _ _ (abs-ap _ _ _) f) a) x) =>
        (Ok ((ap ? ? (ap ? ? f x) (ap ? ? a x)), (abs-ap-eq ? ? ? f a x)))
      | _ => (Error "no")
      end
    try-to-rule : (Term -> (Result (Term, Term))) = fun term =>
      match term with
      | (ap _ _ (ap _ _ (ap _ _ (abs-to _) A) B) x) =>
        (Ok ((to (ap ? ? A x) (ap ? ? B x)), (abs-to-eq ? A B x)))
      | _ => (Error "no")
      end
    try-eq-rule : (Term -> (Result (Term, Term))) = fun term =>
      match term with
      | (ap _ _ (ap _ _ (ap _ _ (abs-eq _) A) B) x) =>
        (Ok ((eq ? ? (ap ? ? A x) (ap ? ? B x)), (abs-eq-eq ? A B x)))
      | _ => (Error "no")
      end
    -- Try every #reduction-tagged rule at the top of `term`; first hit wins.
    try-top : ((List Signature) -> (Term -> (Result (Term, Term)))) = fun ctx => fun term =>
      let step1 =
        if (rule-enabled abs-ident-eq ctx) then (try-ident term) else (Error "off") end in
      let step2 = match step1 with
        | Ok _ => step1
        | Error _ =>
          if (rule-enabled abs-const-eq ctx) then (try-const term) else step1 end
        end in
      let step3 = match step2 with
        | Ok _ => step2
        | Error _ =>
          if (rule-enabled abs-ap-eq ctx) then (try-apf term) else step2 end
        end in
      let step4 = match step3 with
        | Ok _ => step3
        | Error _ =>
          if (rule-enabled abs-to-eq ctx) then (try-to-rule term) else step3 end
        end in
      match step4 with
      | Ok _ => step4
      | Error _ =>
        if (rule-enabled abs-eq-eq ctx) then (try-eq-rule term) else step4 end
      end
    -- Recursive normalising reducer. Returns (normal-form,
    -- proof : eq term normal-form). Innermost-first; after subterms
    -- settle, try a top-level rule; if one fires, recurse on the result.
    beta-reduce : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun term =>
      let sub = match term with
        | (ap A B f a) =>
          let fr = (beta-reduce ctx f) in
          let ar = (beta-reduce ctx a) in
          let f2 = (fst fr) in
          let fp = (snd fr) in
          let a2 = (fst ar) in
          let aproof = (snd ar) in
          ((ap A B f2 a2), (ap (ap cong-ap fp) aproof))
        | (to A B) =>
          let ar = (beta-reduce ctx A) in
          let br = (beta-reduce ctx B) in
          let A2 = (fst ar) in
          let Apf = (snd ar) in
          let B2 = (fst br) in
          let Bpf = (snd br) in
          ((to A2 B2), (cong-to Apf Bpf))
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
    -- Coerce hook: reduce BOTH sides to a (hopefully common) normal
    -- form, then chain `eq found nf` with `sym (eq expected nf)` to
    -- build `eq found expected`. The verify pass unifies — if the two
    -- normal forms agree (or are unifiable up to metas), the cast
    -- type-checks.
    coerce beta = fun ctx => fun expected => fun found => fun contents =>
      let fr = (beta-reduce ctx found) in
      let er = (beta-reduce ctx expected) in
      let full = (ap (ap trans (snd fr)) (ap sym (snd er))) in
      (Ok (ap (ap cast full) contents))
    schema unit-schema =
        fun ctx => fun s => 
          match s with 
          | [_, (_,_,_,_), _, _] =>
          (Ok [
            ?,
            ?,
            ?,
            ?
            ])
          | _ => (Error "invalid")
          end
-- construct by unit-schema
postulate
unit : U
unit-star : unit
unit-rec : pi (ap (ap abs-to (ap abs-const unit)) (ap (ap abs-to abs-ident) abs-ident))
unit-rec-eq (M : U) (star-case : M) : 
  eq M M (ap (ap 
    (dap unit-rec M)
     unit-star) star-case) star-case

    -- (ap (ap cast ?) (dap unit-rec M))
    
-- doesn't work because the motive needs to be abstractible
-- construct by unit-schema
-- unit : U
-- unit-star : unit
-- unit-rec (M : U) : to unit (to M M)
-- unit-rec-eq (M : U) (star-case : M) : eq (ap (ap (unit-rec M) unit-star) star-case) star-case
