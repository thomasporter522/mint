type termMeta = {
  parens: bool,
  start: int,
  end_: int,
};

type cTerm =
  | Shard(Grammar.primaryToken)
  | Hole(bool)
  | Identifier(string)
  | StringLit(string)
  | Asc(term, term)
  | Arrow(term, term)
  | Eq(term, term)
  | Comma(term, term)
  | BinOp(string, term, term)
  | Ap(term, list(term))
  | List(list(term))
  | Fun(term, term)                          /* fun pat => body */
  | Match(term, list((term, term)))          /* match scrut with branches */
  | If(term, term, term)                     /* if cond then thenBr else elseBr */
  | Postulate(list(term), option(term))
  | Schema(option(term))
  | Construct(term, list(term), option(term))
  | BuilderError
and term = {
  value: cTerm,
  meta: termMeta,
};

let defaultMeta = {parens: false, start: (-1), end_: (-1)};

let mk = (t: cTerm): term => {value: t, meta: defaultMeta};
