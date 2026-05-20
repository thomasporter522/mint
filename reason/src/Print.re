open Term;

let printBinOp =
  fun
  | Eq => "=="
  | Neq => "!="
  | And => "&&"
  | Or => "||";

/* --- OL printers --- */

let rec printOL = (t: ol): string => {
  /* When an Ap's head or arg is itself a parens-less Ap, the result
     re-parses with a different shape (`f (g x) y` → 3 args vs.
     `f g x y` → 4 args). Wrap such children so the print round-trips
     and the displayed structure is unambiguous. */
  let pchild = (s: ol): string => {
    switch (s.value) {
    | OLAp(_, _) when !s.meta.parens => "(" ++ printOL(s) ++ ")"
    | _ => printOL(s)
    }
  };
  let inner =
    switch (t.value) {
    | OLHole(User) => "?"
    | OLHole(Synthesized) => ""
    | OLHole(Auto) => "\xE2\x9F\x90"  /* U+27D0 ⟐ as raw UTF-8 bytes */
    | OLMeta(_) => "?"  /* user never sees meta IDs */
    | OLIdentifier(v) => v
    | OLAp(f, args) =>
      pchild(f) ++ " " ++ String.concat(" ", List.map(pchild, args))
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugOL = (t: ol): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | OLHole(User) => "Hole"
  | OLHole(Synthesized) => "Hole_"
  | OLHole(Auto) => "Auto"
  | OLMeta(id) => "Meta(" ++ string_of_int(id) ++ ")"
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
    | Hole(User) => "?"
    | Hole(Synthesized) => ""
    | Hole(Auto) => "\xE2\x9F\x90"
    | TagLit(name) => "#" ++ name
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
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugML = (t: ml): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | Hole(User) => "Hole"
  | Hole(Synthesized) => "Hole_"
  | Hole(Auto) => "Auto"
  | Identifier(v) => "Id(" ++ v ++ ")"
  | StringLit(s) => "Str(" ++ s ++ ")"
  | TagLit(name) => "Tag(#" ++ name ++ ")"
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
  };
};

/* --- Declaration and block printers ---
   We preserve the outer `parens` flag on retType/paramType so a round-
   trip through the parser produces the same AST. Stripping would have
   the printer output `Ul` for a stored `(Ul)` (parens=true), and the
   re-parse would see a paren-less form — breaking elaboration
   idempotence whenever the parens flag carries semantic weight (e.g.
   the parenthesized-singleton constructor-elaboration trigger). */

let printParam = (p: param): string =>
  "(" ++ p.paramName ++ " : " ++ printOL(p.paramType) ++ ")";

let printDecl = (d: decl): string =>
  switch (d.params) {
  | [] => d.declName ++ " : " ++ printOL(d.retType)
  | params =>
    d.declName ++ " " ++ String.concat(" ", List.map(printParam, params))
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
  | CoerceDef(b) => "coerce " ++ printBinding(b)
  | NewtagDef(tag, _) => "newtag #" ++ tag
  };

let printTagLine = (t: tagLine): string =>
  "#" ++ t.tag ++ " " ++ t.target;

let printBlock = (b: block): string => {
  let printDecls = (decls, tagLines) => {
    let dStrs = List.map(printDecl, decls);
    let tStrs = List.map(printTagLine, tagLines);
    String.concat("\n", dStrs @ tStrs);
  };
  switch (b) {
  | Postulate(_, decls, tagLines) => "postulate\n" ++ printDecls(decls, tagLines)
  | Meta(defs) => "meta\n" ++ String.concat("\n", List.map(printMetaDef, defs))
  | Construct(schemaName, _, _, decls, tagLines) =>
    "construct by " ++ schemaName ++ "\n" ++ printDecls(decls, tagLines)
  };
};

let printProgram = (p: program): string =>
  String.concat("\n", List.map(printBlock, p)) ++ "\n";
