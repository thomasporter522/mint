open Grammar;

type termMeta = {
  parens: bool,
  start: int,
  end_: int,
};

type cTerm =
  | Shard(primaryToken)
  | Hole(bool)
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

let defaultMeta = {parens: false, start: (-1), end_: (-1)};

let mk = (t: cTerm): term => {value: t, meta: defaultMeta};
