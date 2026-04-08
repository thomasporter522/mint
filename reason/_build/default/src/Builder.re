open Utils;
open Grammar;
open Term;
open Parser;

let combineTerms =
  fun
  | [] => mk(Hole(true))
  | [t] => t
  | [first, ..._] as ts => {
      let last = List.nth(ts, List.length(ts) - 1);
      let t = mk(Ap(first, List.tl(ts)));
      {...t, meta: {...t.meta, start: first.meta.start, end_: last.meta.end_}};
    };

let localize = (t: term, token: ranged(primaryToken)): term =>
  {...t, meta: {...t.meta, start: token.start, end_: token.end_}};

let isToken = (name: string, tok: primaryToken): bool =>
  switch (tok) {
  | TNamed(n) => n == name
  | _ => false
  };

let rec buildTerms = (fs: list(sharded(openForm))): term =>
  combineTerms(List.concat_map(buildSharded, fs))

and buildChild = (unforms, form) =>
  combineTerms(
    switch (form) {
    | Some(f) => buildUnforms(unforms) @ [buildForm(f)]
    | None => buildUnforms(unforms)
    },
  )

and buildItems = (items: list(sharded(openForm))): list(term) =>
  List.filter_map(
    fun
    | Unform(_) => None
    | Form(f) => Some(buildForm(f)),
    items,
  )

and faceToken = (form: closedForm): string =>
  switch (form) {
  | CMatch(_, _, {value: TNamed(n), _}) => n
  | CHead({value: TNamed(n), _}) => n
  | _ => ""
  }

and buildBlock = (keyword, contents, rest): term => {
  let body = buildItems(contents);
  switch (keyword) {
  | "postulate" => mk(Postulate(body, rest))
  | "schema" => mk(Schema(rest))
  | "construct" =>
    switch (body) {
    | [by, ...decls] => mk(Construct(by, decls, rest))
    | [] => mk(Construct(mk(Hole(true)), [], rest))
    }
  | _ => mk(BuilderError)
  };
}

and buildBlocks = (form, contents, rest): term => {
  let keyword = faceToken(form);
  switch (form) {
  | CHead(_) => buildBlock(keyword, contents, rest)
  | CMatch(inner, innerItems, _) =>
    buildBlocks(inner, innerItems, Some(buildBlock(keyword, contents, rest)))
  };
}

and buildLeftChild = (left, leftUf) =>
  combineTerms(
    switch (left) {
    | Some(f) => [buildForm(f), ...buildUnforms(leftUf)]
    | None => buildUnforms(leftUf)
    },
  )

and buildInfix = (constructor, left, leftUf, tok, rightUf, right) =>
  localize(mk(constructor(buildLeftChild(left, leftUf), buildChild(rightUf, right))), tok)

/* Collect comma-separated items from a right-nested Comma tree */
and collectCommaItems = (t: term): list(term) =>
  switch (t.value) {
  | Comma(l, r) when !t.meta.parens => [l, ...collectCommaItems(r)]
  | _ => [t]
  }

/* Check if a closed form is a match...with...|...=> chain */
and isMatchChain = (cf: closedForm): bool =>
  switch (cf) {
  | CMatch(inner, _, {value: TNamed("end" | "=>" | "|" | "with"), _}) =>
    isMatchChain(inner)
  | CHead({value: TNamed("match"), _}) => true
  | _ => false
  }

/* Walk a match chain and extract: scrutinee + list of (pattern, body) branches.
   Chain structure: CMatch(CMatch(...CMatch(CHead(match), [scrut], with)..., [pat], =>), [body], |/end)
   Alternating: match(scrut)with()|(pat)=>(body)|(pat)=>(body)end */
and collectMatchBranches = (cf: closedForm): (term, list((term, term))) =>
  switch (cf) {
  /* Base: match(scrutinee)with */
  | CMatch(CHead({value: TNamed("match"), _}), scrutItems, {value: TNamed("with"), _}) =>
    (buildTerms(scrutItems), [])
  /* (body)end or (body)| — outermost has the body, inner has the pattern */
  | CMatch(inner, bodyItems, {value: TNamed("end" | "|"), _}) =>
    let body = buildTerms(bodyItems);
    switch (inner) {
    /* (pat)=> — pattern captured between | and => */
    | CMatch(deeper, patItems, {value: TNamed("=>"), _}) =>
      let pat = buildTerms(patItems);
      let (scrutinee, prevBranches) = collectMatchBranches(deeper);
      (scrutinee, prevBranches @ [(pat, body)])
    | _ =>
      collectMatchBranches(inner)
    }
  /* ()| — skip empty levels (e.g. with()| connector) */
  | _ => (mk(Hole(true)), [])
  }

and buildMatchChain = (cf: closedForm, rightUf, right): term => {
  let (scrutinee, branches) = collectMatchBranches(cf);
  let branchTerms =
    List.map(
      ((pat, body)) => mk(FatArrow(pat, body)),
      branches,
    );
  let branchPipe =
    switch (branchTerms) {
    | [] => mk(Hole(true))
    | [first, ...rest] =>
      List.fold_left((acc, b) => mk(Pipe(acc, b)), first, rest)
    };
  let matchTerm = mk(Ap(mk(Identifier("match")), [scrutinee, mk(Identifier("with")), branchPipe]));
  /* If there's content after end, wrap in application */
  let rest = buildChild(rightUf, right);
  switch (rest.value) {
  | Hole(true) => matchTerm
  | _ => mk(Ap(matchTerm, [rest]))
  };
}

and buildForm = (form: openForm): term => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* parenthesized expression */
  | (None, [], CMatch(CHead({value: TNamed("("), _}), items, {value: TNamed(")"), _}), [], None) =>
    let t = buildTerms(items);
    {...t, meta: {...t.meta, parens: true}};

  /* list literal [...] */
  | (None, [], CMatch(CHead({value: TNamed("["), _}), items, {value: TNamed("]"), _}), [], None) =>
    let inner = buildTerms(items);
    mk(Term.List(collectCommaItems(inner)));

  /* atoms */
  | (None, [], CHead({value: TAtom(Hole), _} as tok), [], None) =>
    localize(mk(Term.Hole(false)), tok)
  | (None, [], CHead({value: TAtom(Identifier(v)), _} as tok), [], None) =>
    localize(mk(Term.Identifier(v)), tok)
  | (None, [], CHead({value: TAtom(StringLit(s)), _} as tok), [], None) =>
    localize(mk(Term.StringLit(s)), tok)

  /* fun...=> lambda — body is the right child via =>_face's precedence */
  | (_, _, CMatch(CHead({value: TNamed("fun"), _}), patItems, {value: TNamed("=>"), _}), _, _) =>
    let pat = buildTerms(patItems);
    let body = buildChild(rightUf, right);
    mk(FatArrow(mk(Ap(mk(Identifier("fun")), [pat])), body));

  /* infix operators */
  | (_, _, CHead({value: TNamed(":"), _} as tok), _, _) =>
    buildInfix((l, r) => Asc(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("->"), _} as tok), _, _) =>
    buildInfix((l, r) => Arrow(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("="), _} as tok), _, _) =>
    buildInfix((l, r) => Eq(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("=>"), _} as tok), _, _) =>
    buildInfix((l, r) => FatArrow(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed(","), _} as tok), _, _) =>
    buildInfix((l, r) => Comma(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("|"), _} as tok), _, _) =>
    buildInfix((l, r) => Pipe(l, r), left, leftUf, tok, rightUf, right)

  /* keywords that are just atoms (fun, match, with, if, then, else, _) */
  | (None, [], CHead({value: TNamed(name), _} as tok), [], None) =>
    localize(mk(Term.Identifier(name)), tok)

  /* catch-all infix: any named operator with children */
  | (_, _, CHead({value: TNamed(op), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(op, l, r), left, leftUf, tok, rightUf, right)

  /* match...with...|...=>...end chain */
  | (_, _, CMatch(_, _, {value: TNamed("end"), _}), _, _)
      when isMatchChain(closed) =>
    buildMatchChain(closed, rightUf, right)

  /* blocks terminated by `end` */
  | (_, _, CMatch(inner, innerItems, {value: TNamed("end"), _}), [], None) =>
    buildBlocks(inner, innerItems, None)

  | _ => mk(BuilderError)
  };
}

and buildUnform =
  fun
  | USecondary(_) => []
  | UShard(token) => [mk(Shard(token.value))]

and buildUnforms = unforms => List.concat_map(buildUnform, unforms)

and buildSharded =
  fun
  | Unform(u) => buildUnform(u)
  | Form(f) => [buildForm(f)];

let build = (forms: list(sharded(openForm))): term => buildTerms(forms);
