open Grammar;
open Term;

let printAtom =
  fun
  | Grammar.Hole => "?"
  | Identifier(v) => v;

let printPrimaryToken =
  fun
  | BOF | EOF   => ""
  | TOP         => "("
  | TCP         => ")"
  | TAtom(a)    => printAtom(a)
  | TColon      => ":"
  | TPostulate  => "postulate"
  | TSchema   => "schema"
  | TConstruct  => "construct"
  | TEnd        => "end";

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
    | Asc(left, right) =>
      printTerm(left) ++ " : " ++ printTerm(right)
    | Ap(f, args) =>
      printTerm(f) ++ " " ++ String.concat(" ", List.map(printTerm, args))
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
