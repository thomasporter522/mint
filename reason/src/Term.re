open Grammar;

type termMeta = {
  parens: bool,
  start: int,
  end_: int,
};

type cTerm =
  | Shard(primaryToken)
  | Hole(bool) /* inserted */
  | Identifier(string)
  | Asc(term, term)
  | Ap(term, list(term))
  | Postulate(list(term), option(term))
  | Checker(option(term))
  | Construct(term, list(term), option(term))
  | BuilderError
and term = {
  value: cTerm,
  meta: termMeta,
};

let meta = (t: cTerm): term => {
  {value: t, meta: {parens: false, start: (-1), end_: (-1)}};
};
