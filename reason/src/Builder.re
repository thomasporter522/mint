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

let isCommaToken = (tok: primaryToken): bool =>
  switch (tok) {
  | TNamed("," | ",p" | ",l") => true
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

/* --- Block builders --- */

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
  | "meta" => mk(Meta(body, rest))
  | "construct" =>
    switch (body, rest) {
    | ([], Some(r)) => r  /* construct by ... — real content is in the "by" block */
    | ([by, ...decls], _) => mk(Construct(by, decls, rest))
    | ([], None) => mk(Construct(mk(Hole(true)), [], rest))
    }
  | "by" =>
    switch (body) {
    | [name, ...decls] => mk(Construct(name, decls, rest))
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

/* --- Match chain: match(scrut)with()|(pat)=>(body)|(pat)=>(body)end --- */

and isMatchChain = (cf: closedForm): bool =>
  switch (cf) {
  | CMatch(inner, _, {value: TNamed("end" | "=>" | "|" | "with"), _}) =>
    isMatchChain(inner)
  | CHead({value: TNamed("match"), _}) => true
  | _ => false
  }

and collectMatchBranches = (cf: closedForm): (term, list((term, term))) =>
  switch (cf) {
  | CMatch(CHead({value: TNamed("match"), _}), scrutItems, {value: TNamed("with"), _}) =>
    (buildTerms(scrutItems), [])
  | CMatch(inner, bodyItems, {value: TNamed("end" | "|"), _}) =>
    let body = buildTerms(bodyItems);
    switch (inner) {
    | CMatch(deeper, patItems, {value: TNamed("=>"), _}) =>
      let pat = buildTerms(patItems);
      let (scrutinee, prevBranches) = collectMatchBranches(deeper);
      (scrutinee, prevBranches @ [(pat, body)])
    | _ =>
      collectMatchBranches(inner)
    }
  | _ => (mk(Hole(true)), [])
  }

/* --- If chain: if(cond)then(thenBr)else(elseBr)end --- */

and isIfChain = (cf: closedForm): bool =>
  switch (cf) {
  | CMatch(inner, _, {value: TNamed("end" | "else" | "then"), _}) =>
    isIfChain(inner)
  | CHead({value: TNamed("if"), _}) => true
  | _ => false
  }

and buildIfChain = (cf: closedForm): term =>
  switch (cf) {
  | CMatch(CMatch(CMatch(CHead({value: TNamed("if"), _}), condItems, {value: TNamed("then"), _}), thenItems, {value: TNamed("else"), _}), elseItems, {value: TNamed("end"), _}) =>
    mk(If(buildTerms(condItems), buildTerms(thenItems), buildTerms(elseItems)))
  | _ => mk(BuilderError)
  }

/* --- Bracket elements: walk comma chain --- */

and collectBracketElements = (cf: closedForm): (string, list(list(sharded(openForm)))) =>
  switch (cf) {
  | CHead({value: TNamed(open_), _}) => (open_, [])
  | CMatch(inner, items, {value, _}) when isCommaToken(value) || value == TNamed(")") || value == TNamed("]") =>
    let (open_, prev) = collectBracketElements(inner);
    (open_, prev @ [items])
  | _ => ("", [])
  }

/* === Main builder === */

and buildForm = (form: openForm): term => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* Bracket forms: (...), [...], with commas */
  | (None, [], CMatch(_, _, {value: TNamed(")" | "]"), _}), [], None) =>
    let (open_, elementGroups) = collectBracketElements(closed);
    let elements = List.map(buildTerms, elementGroups);
    switch (open_, elements) {
    | ("(", [single]) => {...single, meta: {...single.meta, parens: true}}
    | ("(", elements) =>
      let rec buildComma =
        fun
        | [] => mk(Hole(true))
        | [single] => single
        | [first, ...rest] => mk(Comma(first, buildComma(rest)));
      let t = buildComma(elements);
      {...t, meta: {...t.meta, parens: true}}
    | ("[", items) =>
      /* Check if last element is a spread: ...rest */
      switch (List.rev(items)) {
      | [{value: Ap({value: Identifier("..."), _}, [tail]), _}, ...revHeads] =>
        mk(Term.Cons(List.rev(revHeads), tail))
      | [{value: Identifier("..."), _}, ...revHeads] =>
        /* bare [...] with no tail identifier — treat as empty spread */
        mk(Term.Cons(List.rev(revHeads), mk(Term.List([]))))
      | [{value: Hole(true), _}] =>
        /* [] with nothing inside — empty list */
        mk(Term.List([]))
      | _ => mk(Term.List(items))
      }
    | _ => mk(BuilderError)
    };

  /* Atoms */
  | (None, [], CHead({value: TAtom(Hole), _} as tok), [], None) =>
    localize(mk(Term.Hole(false)), tok)
  | (None, [], CHead({value: TAtom(Identifier(v)), _} as tok), [], None) =>
    localize(mk(Term.Identifier(v)), tok)
  | (None, [], CHead({value: TAtom(StringLit(s)), _} as tok), [], None) =>
    localize(mk(Term.StringLit(s)), tok)

  /* fun(pat)=> — body captured by =>_face's right-precedence */
  | (_, _, CMatch(CHead({value: TNamed("fun"), _}), patItems, {value: TNamed("=>" | "=>f"), _}), _, _) =>
    let pat = buildTerms(patItems);
    let body = buildChild(rightUf, right);
    mk(Fun(pat, body))

  /* let(binding)in — body captured by in_face's right-precedence */
  | (_, _, CMatch(CHead({value: TNamed("let"), _}), bindingItems, {value: TNamed("in"), _}), _, _) =>
    let binding = buildTerms(bindingItems);
    let body = buildChild(rightUf, right);
    mk(Let(binding, body))

  /* Infix operators */
  | (_, _, CHead({value: TNamed(":"), _} as tok), _, _) =>
    buildInfix((l, r) => Asc(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("->"), _} as tok), _, _) =>
    buildInfix((l, r) => Arrow(l, r), left, leftUf, tok, rightUf, right)
  | (_, _, CHead({value: TNamed("="), _} as tok), _, _) =>
    buildInfix((l, r) => Eq(l, r), left, leftUf, tok, rightUf, right)

  /* Keyword atoms */
  | (None, [], CHead({value: TNamed(name), _} as tok), [], None) =>
    localize(mk(Term.Identifier(name)), tok)

  /* Catch-all infix */
  | (_, _, CHead({value: TNamed(op), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(op, l, r), left, leftUf, tok, rightUf, right)

  /* match...with...|...=>...end */
  | (_, _, CMatch(_, _, {value: TNamed("end"), _}), _, _) when isMatchChain(closed) =>
    buildMatchChain(closed)

  /* if...then...else...end */
  | (_, _, CMatch(_, _, {value: TNamed("end"), _}), _, _) when isIfChain(closed) =>
    buildIfChain(closed)

  /* Other blocks terminated by `end` */
  | (_, _, CMatch(inner, innerItems, {value: TNamed("end"), _}), [], None) =>
    buildBlocks(inner, innerItems, None)

  | _ => mk(BuilderError)
  };
}

and buildMatchChain = (cf: closedForm): term => {
  let (scrutinee, branches) = collectMatchBranches(cf);
  mk(Match(scrutinee, branches));
}

and buildUnform =
  fun
  | USecondary(_) => []
  | UShard(token) => [localize(mk(Shard(token.value)), token)]

and buildUnforms = unforms => List.concat_map(buildUnform, unforms)

and buildSharded =
  fun
  | Unform(u) => buildUnform(u)
  | Form(f) => [buildForm(f)];

let build = (forms: list(sharded(openForm))): term => buildTerms(forms);
