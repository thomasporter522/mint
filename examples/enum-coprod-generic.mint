-- Generic coproduct-based enums via iterated Either
postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq A A a a
trans (A : U) (a : A) (b : A) (c : A) (e1 : eq A A a b) (e2 : eq A A b c) : eq A A a c
Arr (A : U) (B : U) : U
app (A : U) (B : U) (f : Arr A B) (a : A) : B
const (A : U) (B : U) (b : B) : Arr A B
const-beta (A : U) (B : U) (b : B) (a : A) : eq B B (app A B (const A B b) a) b
Void : U
absurd (M : U) (v : Void) : M
Unit : U
star : Unit
unit-rec (M : U) (star-case : M) (u : Unit) : M
unit-comp (M : U) (star-case : M) : eq M M (unit-rec M star-case star) star-case
Either (A : U) (B : U) : U
inl (A : U) (B : U) (a : A) : Either A B
inr (A : U) (B : U) (b : B) : Either A B
either (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) : Arr (Either A B) M
either-inl (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (a : A) : eq M M (app (Either A B) M (either A B M f g) (inl A B a)) (app A M f a)
either-inr (A : U) (B : U) (M : U) (f : Arr A M) (g : Arr B M) (b : B) : eq M M (app (Either A B) M (either A B M f g) (inr A B b)) (app B M g b)
meta
reverse : ((List Term) -> (List Term)) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs)
reverse-triples : ((List (Term, (Term, Term))) -> (List (Term, (Term, Term)))) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs)
append : ((List Term) -> ((List Term) -> (List Term))) = fun xs => fun ys => (foldl (fun acc => fun x => x :: acc) ys (reverse xs))
concat : ((List (List Term)) -> (List Term)) = fun xss => (foldl (fun acc => fun xs => (append acc xs)) [] xss)

build-injs-and-type : ((List Term) -> ((List Term), Term)) = fun rest =>
  (foldl (fun acc => fun _ =>
    let prev-injs = (fst acc) in
    let prev-type = (snd acc) in
    let cur-type = (Either Unit prev-type) in
    let wrapped = (reverse (foldl (fun a => fun inj =>
      (inr Unit prev-type inj) :: a) [] prev-injs)) in
    ((inl Unit prev-type star) :: wrapped, cur-type)
  ) ([star], Unit) rest)

build-elim : (Term -> ((List Term) -> ((List Term) -> Term))) = fun mvar => fun case-vars => fun rest =>
  let rev-cvs = (reverse case-vars) in
  match rev-cvs with
  | last-cv :: remaining-cvs =>
    (fst (foldl (fun acc => fun cv =>
      let prev-arr = (fst acc) in
      let prev-type = (snd acc) in
      ((either Unit prev-type mvar (const Unit mvar cv) prev-arr),
       (Either Unit prev-type))
    ) ((const Unit mvar last-cv), Unit) remaining-cvs))
  | _ => (const Unit mvar star)
  end

-- Build equation proofs.
-- Tracks triples: (proof-term, injection-term, target-tc)
-- Fold from innermost (last ctor) outward.
build-proofs : (Term -> ((List Term) -> ((List Term) -> (List Term)))) = fun mvar => fun case-vars => fun rest =>
  let rev-cvs = (reverse case-vars) in
  match rev-cvs with
  | last-cv :: remaining-cvs =>
    -- Accumulator: (triples-list, elim-arr, inner-type)
    -- Each triple: (proof, injection, target-tc)
    -- Innermost: proof = const-beta, inj = star, tc = last-cv
    let result = (foldl (fun acc => fun cv =>
      let prev-triples = (fst (fst acc)) in
      let prev-elim = (snd (fst acc)) in
      let prev-type = (snd acc) in
      let cur-type = (Either Unit prev-type) in
      let f = (const Unit mvar cv) in
      let cur-elim = (either Unit prev-type mvar f prev-elim) in
      -- New triple for inl (this constructor):
      let inl-proof = (trans mvar
        (app cur-type mvar cur-elim (inl Unit prev-type star))
        (app Unit mvar f star)
        cv
        (either-inl Unit prev-type mvar f prev-elim star)
        (const-beta Unit mvar cv star)) in
      let inl-triple = (inl-proof, ((inl Unit prev-type star), cv)) in
      -- Wrap existing triples with inr:
      -- Wrap existing triples with inr:
      let wrapped = (reverse-triples (foldl (fun a => fun triple =>
        let old-proof = (fst triple) in
        let old-inj = (fst (snd triple)) in
        let old-tc = (snd (snd triple)) in
        let new-proof = (trans mvar
          (app cur-type mvar cur-elim (inr Unit prev-type old-inj))
          (app prev-type mvar prev-elim old-inj)
          old-tc
          (either-inr Unit prev-type mvar f prev-elim old-inj)
          old-proof) in
        (new-proof, ((inr Unit prev-type old-inj), old-tc)) :: a
      ) [] prev-triples)) in
      ((inl-triple :: wrapped, cur-elim), cur-type)
    ) (([((const-beta Unit mvar last-cv star), (star, last-cv))],
        (const Unit mvar last-cv)), Unit) remaining-cvs) in
    -- Extract just the proof terms
    (reverse (foldl (fun acc => fun triple =>
      (fst triple) :: acc) [] (fst (fst result))))
  | _ => []
  end

schema enum = fun s => match s with
  | [(type-name, [], U),
     (case-name, [(mvar, U), (scrut, type-name)], mvar)]
    => (Ok [Void, (absurd mvar scrut)])
  | [(type-name, [], U),
     (ctor, [], type-name),
     (case-name, [(mvar, U), (tc, mvar), (scrut, type-name)], mvar),
     (eq-name, [(mvar2, U), (tc2, mvar2)], _)]
    => (Ok [Unit, star, (unit-rec mvar tc scrut), (unit-comp mvar2 tc2)])
  | (type-name, [], U) :: all-rest =>
    -- Find case params: scan for first entry with non-empty params.
    -- Seed with [(star, star)] to establish List (Term, Term) element type.
    let found-params = (foldl (fun acc => fun entry =>
      if (fst acc) == true then acc
      else match entry with
        | (_, [], _) => acc
        | (_, params, _) => (true, params)
        end
      end
    ) (false, [(star, star)]) all-rest) in
    match (snd found-params) with
    | (mvar, U) :: tc-and-scrut =>
      -- Extract case-vars and scrut: foldl collects names, last one is the scrutinee.
      -- case-vars end up in reverse order, matching what build-elim/build-proofs need.
      let vars-info = (foldl (fun acc => fun p =>
        if (fst (fst acc)) == true
        then ((false, (snd (fst acc))), (fst p))
        else ((false, (snd acc) :: (snd (fst acc))), (fst p))
        end
      ) ((true, []), star) tc-and-scrut) in
      let rev-case-vars = (snd (fst vars-info)) in
      let scrut = (snd vars-info) in
      -- case-vars is in original order (foldl reverses rev-tcs, then we reverse back)
      let case-vars = (reverse rev-case-vars) in
      match case-vars with
      | _ :: rest-case-vars =>
        let iat = (build-injs-and-type rest-case-vars) in
        let injs = (fst iat) in
        let coprod-type = (snd iat) in
        let elim-arr = (build-elim mvar case-vars rest-case-vars) in
        let case-witness = (app coprod-type mvar elim-arr scrut) in
        let proofs = (build-proofs mvar case-vars rest-case-vars) in
        (Ok (concat [[coprod-type], injs, [case-witness], proofs]))
      | _ => (Error "no ctors") end
    | _ => (Error "bad params") end
  | _ => (Error "unrecognized") end
construct by enum
falsity : U
falsity-case (M : U) (scrutinee : falsity) : M
construct by enum
unit : U
trivial : unit
unit-case (M : U) (trivial-case : M) (scrutinee : unit) : M
unit-case-trivial (M : U) (trivial-case : M) : eq M M (unit-case M trivial-case trivial) trivial-case
construct by enum
mybool : U
yes : mybool
no : mybool
mybool-case (M : U) (yes-case : M) (no-case : M) (scrutinee : mybool) : M
mybool-case-yes (M : U) (yes-case : M) (no-case : M) : eq M M (mybool-case M yes-case no-case yes) yes-case
mybool-case-no (M : U) (yes-case : M) (no-case : M) : eq M M (mybool-case M yes-case no-case no) no-case
end

construct by enum
triple : U
a : triple
b : triple
c : triple
triple-case (M : U) (a-case : M) (b-case : M) (c-case : M) (scrutinee : triple) : M
triple-case-a (M : U) (a-case : M) (b-case : M) (c-case : M) : eq M M (triple-case M a-case b-case c-case a) a-case
triple-case-b (M : U) (a-case : M) (b-case : M) (c-case : M) : eq M M (triple-case M a-case b-case c-case b) b-case
triple-case-c (M : U) (a-case : M) (b-case : M) (c-case : M) : eq M M (triple-case M a-case b-case c-case c) c-case
end
