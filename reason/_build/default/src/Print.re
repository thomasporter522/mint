open Term;

let printPrimaryToken =
  fun
  | Grammar.BOF | Grammar.EOF => ""
  | TAtom(Grammar.Hole) => "?"
  | TAtom(Identifier(v)) => v
  | TAtom(StringLit(s)) => "\"" ++ s ++ "\""
  | TNamed(n) => n;

let rec debugTerm = (t: term): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | Shard(_) => "Shard"
  | Hole(ins) => ins ? "Hole_" : "Hole"
  | Identifier(v) => "Id(" ++ v ++ ")"
  | StringLit(s) => "Str(" ++ s ++ ")"
  | Asc(l, r) => p ++ "Asc(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Arrow(l, r) => p ++ "Arrow(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Eq(l, r) => p ++ "Eq(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Comma(l, r) => p ++ "Comma(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | BinOp(op, l, r) => p ++ "BinOp(" ++ op ++ "," ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Ap(f, args) => p ++ "Ap(" ++ debugTerm(f) ++ ",[" ++ String.concat(",", List.map(debugTerm, args)) ++ "])"
  | List(items) => "List([" ++ String.concat(",", List.map(debugTerm, items)) ++ "])"
  | Fun(pat, body) => "Fun(" ++ debugTerm(pat) ++ "," ++ debugTerm(body) ++ ")"
  | Match(scrut, branches) =>
    "Match(" ++ debugTerm(scrut) ++ ",[" ++
    String.concat(",", List.map(((p, b)) => "(" ++ debugTerm(p) ++ "=>" ++ debugTerm(b) ++ ")", branches)) ++ "])"
  | Let(b, body) => "Let(" ++ debugTerm(b) ++ "," ++ debugTerm(body) ++ ")"
  | If(c, t, e) => "If(" ++ debugTerm(c) ++ "," ++ debugTerm(t) ++ "," ++ debugTerm(e) ++ ")"
  | Postulate(body, _) => "Post([" ++ String.concat(",", List.map(debugTerm, body)) ++ "])"
  | Schema(_) => "Schema"
  | Construct(_, _, _) => "Construct"
  | BuilderError => "ERR"
  };
};

let rec printTerm = (t: term): string => {
  let inner =
    switch (t.value) {
    | Shard(token) => printPrimaryToken(token)
    | Hole(inserted) => inserted ? "" : "?"
    | Identifier(v) => v
    | StringLit(s) => "\"" ++ s ++ "\""
    | Asc(left, right) =>
      printTerm(left) ++ " : " ++ printTerm(right)
    | Arrow(left, right) =>
      printTerm(left) ++ " -> " ++ printTerm(right)
    | Eq(left, right) =>
      printTerm(left) ++ " = " ++ printTerm(right)
    | Comma(left, right) =>
      printTerm(left) ++ ", " ++ printTerm(right)
    | BinOp(op, left, right) =>
      printTerm(left) ++ " " ++ op ++ " " ++ printTerm(right)
    | Ap(f, args) =>
      printTerm(f) ++ " " ++ String.concat(" ", List.map(printTerm, args))
    | List(items) =>
      "[" ++ String.concat(", ", List.map(printTerm, items)) ++ "]"
    | Fun(pat, body) =>
      "fun " ++ printTerm(pat) ++ " => " ++ printTerm(body)
    | Match(scrut, branches) =>
      "match " ++ printTerm(scrut) ++ " with"
      ++ String.concat("", List.map(
           ((p, b)) => " | " ++ printTerm(p) ++ " => " ++ printTerm(b),
           branches,
         ))
      ++ " end"
    | Let(binding, body) =>
      "let " ++ printTerm(binding) ++ " in " ++ printTerm(body)
    | If(cond, thenBr, elseBr) =>
      "if " ++ printTerm(cond)
      ++ " then " ++ printTerm(thenBr)
      ++ " else " ++ printTerm(elseBr)
      ++ " end"
    | Postulate(body, rest) =>
      "postulate "
      ++ String.concat("\n", List.map(printTerm, body))
      ++ " end"
      ++ (switch (rest) { | None => "" | Some(r) => " " ++ printTerm(r) })
    | Schema(rest) =>
      "schema"
      ++ (switch (rest) { | None => "" | Some(r) => " " ++ printTerm(r) })
    | Construct(by, body, rest) =>
      "construct " ++ printTerm(by) ++ " "
      ++ String.concat("\n", List.map(printTerm, body))
      ++ " end"
      ++ (switch (rest) { | None => "" | Some(r) => " " ++ printTerm(r) })
    | BuilderError => "<BUILDER ERROR>"
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};
