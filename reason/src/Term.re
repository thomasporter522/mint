type termMeta = {
  parens: bool,
  start: int,
  end_: int,
};

type holeType = 
  | User 
  | Synthesized

type binOp = 
  | Eq 
  | Neq 
  | And 
  | Or

type cPat = 
  | Identifier(string)
  | Wildcard 
and pat = {
  value: cPat,
  meta: termMeta,
};

type cTerm =
  | Shard(Grammar.primaryToken)
  | Hole(holeType)
  | Identifier(string)
  | StringLit(string)
  | Asc(term, term)
  | Arrow(term, term)
  | Eq(term, term)
  | Comma(term, term)
  | BinOp(binOp, term, term)
  | Ap(term, list(term))
  | List(list(term))
  | Cons(term, term)               /* h1 :: tail */
  | Fun(list(pat), term)                          /* fun p1 p2 p3 ... => body */
  | Match(term, list((pat, term)))          /* match scrut with branches */
  | If(term, term, term)                     /* if cond then thenBr else elseBr */
  | Let(pat, option(term), term, term)                          /* let p (: t) = e1 in e2 */
  | Postulate(list(term), option(term))
  | Meta(list(term), option(term))
  | Construct(term, list(term), option(term))
  | BuilderError
and term = {
  value: cTerm,
  meta: termMeta,
};

let defaultMeta = {parens: false, start: (-1), end_: (-1)};

let mk = (t: cTerm): term => {value: t, meta: defaultMeta};
