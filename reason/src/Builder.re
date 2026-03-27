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

and buildBlocks = (form, contents, rest): term =>
  switch (form) {
  | CMatch(_, _, {value: TPostulate, _})
  | CHead({value: TPostulate, _}) =>
    let body = buildItems(contents);
    switch (form) {
    | CHead(_) => mk(Postulate(body, rest))
    | CMatch(inner, innerItems, _) =>
      buildBlocks(inner, innerItems, Some(mk(Postulate(body, rest))))
    };
  | _ => mk(BuilderError)
  }

and buildForm = (form: openForm): term => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* parenthesized expression */
  | (None, [], CMatch(CHead({value: TOP, _}), items, {value: TCP, _}), [], None) =>
    let t = buildTerms(items);
    {...t, meta: {...t.meta, parens: true}};

  /* atoms */
  | (None, [], CHead({value: TAtom(Hole), _} as tok), [], None) =>
    localize(mk(Term.Hole(false)), tok)
  | (None, [], CHead({value: TAtom(Identifier(v)), _} as tok), [], None) =>
    localize(mk(Term.Identifier(v)), tok)

  /* type ascription */
  | (_, _, CHead({value: TColon, _} as tok), _, _) =>
    let l = combineTerms(
      switch (left) {
      | Some(f) => [buildForm(f), ...buildUnforms(leftUf)]
      | None => buildUnforms(leftUf)
      },
    );
    localize(mk(Asc(l, buildChild(rightUf, right))), tok);

  /* blocks terminated by `end` */
  | (_, _, CMatch(inner, innerItems, {value: TEnd, _}), [], None) =>
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
