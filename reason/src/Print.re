open Grammar;
open Term;

let printAtom = (atom: atom): string =>
  switch (atom) {
  | Hole => "?"
  | Identifier(v) => v
  };

let printPrimaryToken = (token: primaryToken): string =>
  switch (token) {
  | BOF
  | EOF => ""
  | TOP => "("
  | TCP => ")"
  | TAtom(a) => printAtom(a)
  | TColon => ":"
  | TPostulate => "postulate"
  | TChecker => "checker"
  | TConstruct => "construct"
  | TEnd => "end"
  };

let rec innerPrintTerm = (t: term): string =>
  switch (t.value) {
  | Shard(token) => printPrimaryToken(token)
  | Hole(inserted) => inserted ? "" : "?"
  | Identifier(v) => v
  | Asc(left, right) =>
    printTerm(left) ++ " : " ++ printTerm(right)
  | Ap(f, args) =>
    printTerm(f)
    ++ " "
    ++ String.concat(" ", List.map(printTerm, args))
  | Postulate(body, rest) =>
    "postulate "
    ++ String.concat("\n", List.map(printTerm, body))
    ++ " end"
    ++ (
      switch (rest) {
      | None => ""
      | Some(r) => " " ++ printTerm(r)
      }
    )
  | Checker(rest) =>
    "checker end"
    ++ (
      switch (rest) {
      | None => ""
      | Some(r) => " " ++ printTerm(r)
      }
    )
  | Construct(by, body, rest) =>
    "construct "
    ++ printTerm(by)
    ++ " "
    ++ String.concat("\n", List.map(printTerm, body))
    ++ " end"
    ++ (
      switch (rest) {
      | None => ""
      | Some(r) => " " ++ printTerm(r)
      }
    )
  | BuilderError => "<BUILDER ERROR>"
  }
and printTerm = (t: term): string => {
  let inner = innerPrintTerm(t);
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};
