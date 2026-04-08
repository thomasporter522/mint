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
