open Term;

let printPrimaryToken =
  fun
  | Grammar.BOF | Grammar.EOF => ""
  | TAtom(Grammar.Hole) => "?"
  | TAtom(Identifier(v)) => v
  | TAtom(StringLit(s)) => "\"" ++ s ++ "\""
  | TNamed(n) => n;

let printBinOp =
  fun
  | Eq => "=="
  | Neq => "!="
  | And => "&&"
  | Or => "||";

/* --- OL printers --- */

let rec printOL = (t: ol): string => {
  let inner =
    switch (t.value) {
    | OLHole(User) => "?"
    | OLHole(Synthesized) => ""
    | OLIdentifier(v) => v
    | OLAp(f, args) =>
      printOL(f) ++ " " ++ String.concat(" ", List.map(printOL, args))
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugOL = (t: ol): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | OLHole(User) => "Hole"
  | OLHole(Synthesized) => "Hole_"
  | OLIdentifier(v) => "Id(" ++ v ++ ")"
  | OLAp(f, args) =>
    p ++ "Ap(" ++ debugOL(f) ++ ",[" ++ String.concat(",", List.map(debugOL, args)) ++ "])"
  };
};

/* --- Pattern printers --- */

let rec printPat = (t: pat): string => {
  let inner =
    switch (t.value) {
    | PWildcard => "_"
    | PVar(s) => s
    | PHole => "?"
    | PString(s) => "\"" ++ s ++ "\""
    | PList(items) =>
      "[" ++ String.concat(", ", List.map(printPat, items)) ++ "]"
    | PCons(head, tail) =>
      printPat(head) ++ " :: " ++ printPat(tail)
    | PTuple(items) =>
      String.concat(", ", List.map(printPat, items))
    | PAp(head, args) =>
      printPat(head) ++ " " ++ String.concat(" ", List.map(printPat, args))
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugPat = (t: pat): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | PWildcard => "Wild"
  | PVar(s) => "PVar(" ++ s ++ ")"
  | PHole => "PHole"
  | PString(s) => "PStr(" ++ s ++ ")"
  | PList(items) =>
    "PList([" ++ String.concat(",", List.map(debugPat, items)) ++ "])"
  | PCons(h, t) =>
    p ++ "PCons(" ++ debugPat(h) ++ "," ++ debugPat(t) ++ ")"
  | PTuple(items) =>
    p ++ "PTuple(" ++ String.concat(",", List.map(debugPat, items)) ++ ")"
  | PAp(head, args) =>
    p ++ "PAp(" ++ debugPat(head) ++ ",[" ++ String.concat(",", List.map(debugPat, args)) ++ "])"
  };
};

/* --- ML printers --- */

let rec printML = (t: ml): string => {
  let inner =
    switch (t.value) {
    | Shard(token) => printPrimaryToken(token)
    | Hole(User) => "?"
    | Hole(Synthesized) => ""
    | Identifier(v) => v
    | StringLit(s) => "\"" ++ s ++ "\""
    | Tuple(items) =>
      String.concat(", ", List.map(printML, items))
    | Asc(l, r) =>
      printML(l) ++ " : " ++ printML(r)
    | BinOp(op, left, right) =>
      printML(left) ++ " " ++ printBinOp(op) ++ " " ++ printML(right)
    /* Infix operators encoded as Ap(Identifier(op), [l, r]) — produced
       by the catch-all in buildForm for operators like ->, =, etc. */
    | Ap({value: Identifier("->"), _}, [l, r]) =>
      printML(l) ++ " -> " ++ printML(r)
    | Ap({value: Identifier("="), _}, [l, r]) =>
      printML(l) ++ " = " ++ printML(r)
    | Ap(f, args) =>
      printML(f) ++ " " ++ String.concat(" ", List.map(printML, args))
    | List(items) =>
      "[" ++ String.concat(", ", List.map(printML, items)) ++ "]"
    | Cons(head, tail) =>
      printML(head) ++ " :: " ++ printML(tail)
    | Fun(pats, body) =>
      "fun " ++ String.concat(" ", List.map(printPat, pats)) ++ " => " ++ printML(body)
    | Match(scrut, branches) =>
      "match " ++ printML(scrut) ++ " with"
      ++ String.concat("", List.map(
           ((p, b)) => " | " ++ printPat(p) ++ " => " ++ printML(b),
           branches,
         ))
      ++ " end"
    | If(cond, thenBr, elseBr) =>
      "if " ++ printML(cond)
      ++ " then " ++ printML(thenBr)
      ++ " else " ++ printML(elseBr)
      ++ " end"
    | Let(b, body) =>
      "let " ++ b.name
      ++ (switch (b.annotation) {
          | Some(ann) => " : " ++ MLType.printType(ann)
          | None => ""
          })
      ++ " = " ++ printML(b.rhs)
      ++ " in " ++ printML(body)
    | BuilderError => "<BUILDER ERROR>"
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugML = (t: ml): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | Shard(_) => "Shard"
  | Hole(User) => "Hole"
  | Hole(Synthesized) => "Hole_"
  | Identifier(v) => "Id(" ++ v ++ ")"
  | StringLit(s) => "Str(" ++ s ++ ")"
  | Tuple(items) =>
    p ++ "Tuple(" ++ String.concat(",", List.map(debugML, items)) ++ ")"
  | Asc(l, r) =>
    p ++ "Asc(" ++ debugML(l) ++ "," ++ debugML(r) ++ ")"
  | BinOp(op, l, r) =>
    p ++ "BinOp(" ++ printBinOp(op) ++ "," ++ debugML(l) ++ "," ++ debugML(r) ++ ")"
  | Ap(f, args) =>
    p ++ "Ap(" ++ debugML(f) ++ ",[" ++ String.concat(",", List.map(debugML, args)) ++ "])"
  | List(items) =>
    "List([" ++ String.concat(",", List.map(debugML, items)) ++ "])"
  | Cons(h, t) =>
    "Cons(" ++ debugML(h) ++ "," ++ debugML(t) ++ ")"
  | Fun(pats, body) =>
    "Fun([" ++ String.concat(",", List.map(debugPat, pats)) ++ "]," ++ debugML(body) ++ ")"
  | Match(scrut, branches) =>
    "Match(" ++ debugML(scrut) ++ ",[" ++
    String.concat(",", List.map(((p, b)) => "(" ++ debugPat(p) ++ "=>" ++ debugML(b) ++ ")", branches)) ++ "])"
  | Let(b, body) =>
    "Let(" ++ b.name ++ "," ++ debugML(b.rhs) ++ "," ++ debugML(body) ++ ")"
  | If(c, t, e) =>
    "If(" ++ debugML(c) ++ "," ++ debugML(t) ++ "," ++ debugML(e) ++ ")"
  | BuilderError => "ERR"
  };
};

/* --- Declaration and block printers --- */

let printParam = (p: param): string =>
  "(" ++ p.paramName ++ " : " ++ printOL(p.paramType) ++ ")";

let printDecl = (d: decl): string =>
  switch (d.params) {
  | [] => d.declName ++ " : " ++ printOL(d.retType)
  | params =>
    "(" ++ d.declName ++ " " ++ String.concat(" ", List.map(printParam, params)) ++ ")"
    ++ " : " ++ printOL(d.retType)
  };

let printBinding = (b: binding): string =>
  b.name
  ++ (switch (b.annotation) {
      | Some(ann) => " : " ++ MLType.printType(ann)
      | None => ""
      })
  ++ " = " ++ printML(b.rhs);

let printMetaDef = (d: metaDef): string =>
  switch (d) {
  | LetDef(b) => printBinding(b)
  | SchemaDef(b) => "schema " ++ printBinding(b)
  };

let printBlock = (b: block): string =>
  switch (b) {
  | Postulate(decls) =>
    "postulate " ++ String.concat("\n", List.map(printDecl, decls)) ++ " end"
  | Meta(defs) =>
    "meta " ++ String.concat("\n", List.map(printMetaDef, defs)) ++ " end"
  | Construct(schemaName, decls) =>
    "construct by " ++ schemaName ++ " "
    ++ String.concat("\n", List.map(printDecl, decls)) ++ " end"
  };

let printProgram = (p: program): string =>
  String.concat(" ", List.map(printBlock, p));

/* --- Backward-compatible aliases --- */

/* These are used by Lytr_api.re and Check.re which still need
   to print ml terms. Will be removed once all consumers are updated. */
let printTerm = printML;
let debugTerm = debugML;
