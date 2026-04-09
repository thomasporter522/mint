open Grammar;
open Term;

let printAtom =
  fun
  | Grammar.Hole => "?"
  | Identifier(v) => v
  | StringLit(s) => "\"" ++ s ++ "\"";

let printPrimaryToken =
  fun
  | BOF | EOF   => ""
  | TAtom(a)    => printAtom(a)
  | TNamed(n)   => n;

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
  | FatArrow(l, r) => p ++ "Fat(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Comma(l, r) => p ++ "Comma(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Pipe(l, r) => p ++ "Pipe(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | BinOp(op, l, r) => p ++ "BinOp(" ++ op ++ "," ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Ap(f, args) => p ++ "Ap(" ++ debugTerm(f) ++ ",[" ++ String.concat(",", List.map(debugTerm, args)) ++ "])"
  | List(items) => "List([" ++ String.concat(",", List.map(debugTerm, items)) ++ "])"
  | Postulate(body, _) => "Post([" ++ String.concat(",", List.map(debugTerm, body)) ++ "])"
  | Schema(_) => "Schema"
  | Construct(_, _, _) => "Construct"
  | BuilderError => "ERR"
  };
};

let rec printRest =
  fun
  | None => ""
  | Some(r) => " " ++ printTerm(r)

and printTerm = (t: term): string => {
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
    | FatArrow(left, right) =>
      printTerm(left) ++ " => " ++ printTerm(right)
    | Comma(left, right) =>
      printTerm(left) ++ ", " ++ printTerm(right)
    | Pipe(left, right) =>
      printTerm(left) ++ " | " ++ printTerm(right)
    | BinOp(op, left, right) =>
      printTerm(left) ++ " " ++ op ++ " " ++ printTerm(right)
    | Ap(f, args) =>
      printTerm(f) ++ " " ++ String.concat(" ", List.map(printTerm, args))
    | List(items) =>
      "[" ++ String.concat(", ", List.map(printTerm, items)) ++ "]"
    | Postulate(body, rest) =>
      "postulate "
      ++ String.concat("\n", List.map(printTerm, body))
      ++ " end" ++ printRest(rest)
    | Schema(rest) =>
      "schema" ++ printRest(rest)
    | Construct(by, body, rest) =>
      "construct " ++ printTerm(by) ++ " "
      ++ String.concat("\n", List.map(printTerm, body))
      ++ " end" ++ printRest(rest)
    | BuilderError => "<BUILDER ERROR>"
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};
