open Utils;
open Grammar;
open Term;
open Parser;

let combineTerms = (ts: list(term)): term =>
  switch (ts) {
  | [] => meta(Hole(true))
  | [t] => t
  | [first, ...rest] =>
    let t = meta(Ap(first, rest));
    let last = List.nth(ts, List.length(ts) - 1);
    {...t, meta: {...t.meta, start: first.meta.start, end_: last.meta.end_}};
  };

let rec buildTerms = (fs: list(sharded(openForm))): term => {
  let ts = List.concat_map(buildSharded, fs);
  combineTerms(ts);
}
and buildLeftChild =
    (form: option(openForm), unforms: unforms): term => {
  let ts =
    switch (form) {
    | Some(f) => [buildForm(f), ...buildUnforms(unforms)]
    | None => buildUnforms(unforms)
    };
  combineTerms(ts);
}
and buildRightChild =
    (unforms: unforms, form: option(openForm)): term => {
  let ts =
    switch (form) {
    | Some(f) => buildUnforms(unforms) @ [buildForm(f)]
    | None => buildUnforms(unforms)
    };
  combineTerms(ts);
}
and buildItem = (item: sharded(openForm)): option(term) =>
  switch (item) {
  | Unform(_) => None
  | Form(f) => Some(buildForm(f))
  }
and buildItems = (items: list(sharded(openForm))): list(term) =>
  List.filter_map(buildItem, items)
and buildBlocks =
    (
      form: closedForm,
      contents: list(sharded(openForm)),
      rest: option(term),
    )
    : term =>
  switch (form) {
  | CMatch(_, _, {value: TPostulate, _})
  | CHead({value: TPostulate, _}) =>
    let body = buildItems(contents);
    switch (form) {
    | CHead(_) => meta(Postulate(body, rest))
    | CMatch(innerForm, innerItems, _) =>
      buildBlocks(innerForm, innerItems, Some(meta(Postulate(body, rest))))
    };
  | _ => meta(BuilderError)
  }
and localize = (t: term, token: ranged(primaryToken)): term => {
  {...t, meta: {...t.meta, start: token.start, end_: token.end_}};
}
and buildForm = (form: openForm): term => {
  let {left, leftUnforms, closedForm: cf, rightUnforms, right} = form;
  let isEmptyUnforms = (u: unforms) => List.length(u) == 0;

  /* parens */
  switch (left, isEmptyUnforms(leftUnforms), cf, isEmptyUnforms(rightUnforms), right) {
  | (None, true, CMatch(CHead({value: TOP, _}), items, {value: TCP, _}), true, None) =>
    let t = buildTerms(items);
    {...t, meta: {...t.meta, parens: true}};
  /* atoms */
  | (None, true, CHead({value: TAtom(atom), _} as token), true, None) =>
    switch (atom) {
    | Hole =>
      let t = meta(Term.Hole(false));
      localize(t, token);
    | Identifier(v) =>
      let t = meta(Term.Identifier(v));
      localize(t, token);
    }
  /* binary operations - colon */
  | (_, _, CHead({value: TColon, _} as token), _, _) =>
    let t =
      meta(
        Asc(
          buildLeftChild(left, leftUnforms),
          buildRightChild(rightUnforms, right),
        ),
      );
    localize(t, token);
  /* blocks with end */
  | (_, _, CMatch(innerForm, innerItems, {value: TEnd, _}), true, None) =>
    buildBlocks(innerForm, innerItems, None)
  | _ => meta(BuilderError)
  };
}
and buildUnform = (u: unform): list(term) =>
  switch (u) {
  | USecondary(_) => []
  | UShard(token) => [meta(Shard(token.value))]
  }
and buildUnforms = (unforms: unforms): list(term) =>
  List.concat_map(buildUnform, unforms)
and buildSharded = (sof: sharded(openForm)): list(term) =>
  switch (sof) {
  | Unform(u) => buildUnform(u)
  | Form(f) => [buildForm(f)]
  };

let build = (forms: list(sharded(openForm))): term => buildTerms(forms);
