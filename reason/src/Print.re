open Term;

let printBinOp =
  fun
  | Eq => "=="
  | Neq => "!="
  | And => "&&"
  | Or => "||";

/* --- OL printers --- */

let rec printOL = (t: ol): string => {
  /* When an Ap's head or arg is itself a parens-less Ap with args, the
     result re-parses with a different shape (`f (g x) y` → 3 args vs.
     `f g x y` → 4 args). Wrap such children so the print round-trips.
     A zero-arg OLAp (a bare identifier) is atomic and doesn't need
     wrapping. */
  let pchild = (s: ol): string => {
    switch (s.value) {
    | OLAp(_, [_, ..._]) when !s.meta.parens => "(" ++ printOL(s) ++ ")"
    | _ => printOL(s)
    }
  };
  let inner =
    switch (t.value) {
    | OLHole => "?"
    | OLMeta(_) => "?"  /* user never sees meta IDs */
    | OLAp(f, []) => f.string
    | OLAp(f, args) =>
      f.string ++ " " ++ String.concat(" ", List.map(pchild, args))
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugOL = (t: ol): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | OLHole => "Hole"
  | OLMeta(id) => "Meta(" ++ string_of_int(id) ++ ")"
  | OLAp(f, args) =>
    p ++ "Ap(" ++ f.string ++ ",[" ++ String.concat(",", List.map(debugOL, args)) ++ "])"
  };
};

/* --- Pattern printers --- */

let rec printPat = (t: pat): string => {
  let inner =
    switch (t.value) {
    | PWildcard => "_"
    | PVar(s) => s
    | PString(s) => "\"" ++ s ++ "\""
    | PList(items) =>
      "[" ++ String.concat(", ", List.map(printPat, items)) ++ "]"
    | PCons(head, tail) =>
      printPat(head) ++ " :: " ++ printPat(tail)
    | PTuple(items) =>
      String.concat(", ", List.map(printPat, items))
    | POLAp(head, []) => head
    | POLAp(head, args) =>
      head ++ " " ++ String.concat(" ", List.map(printPat, args))
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugPat = (t: pat): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | PWildcard => "Wild"
  | PVar(s) => "PVar(" ++ s ++ ")"
  | PString(s) => "PStr(" ++ s ++ ")"
  | PList(items) =>
    "PList([" ++ String.concat(",", List.map(debugPat, items)) ++ "])"
  | PCons(h, t) =>
    p ++ "PCons(" ++ debugPat(h) ++ "," ++ debugPat(t) ++ ")"
  | PTuple(items) =>
    p ++ "PTuple(" ++ String.concat(",", List.map(debugPat, items)) ++ ")"
  | POLAp(head, args) =>
    p ++ "POLAp(" ++ head ++ ",[" ++ String.concat(",", List.map(debugPat, args)) ++ "])"
  };
};

/* --- ML printers --- */

let rec printType =
  fun
  | MOLTerm(ol) => "Term : " ++ printOL(ol)
  | MBool => "Bool"
  | MString => "String"
  | MTag => "Tag"
  | MList(t) => "List " ++ printTypeAtom(t)
  | MResult(t) => "Result " ++ printTypeAtom(t)
  | MTuple(items) => "(" ++ String.concat(", ", List.map(printType, items)) ++ ")"
  | MArrow(a, b) => printTypeAtom(a) ++ " -> " ++ printTypeAtom(b)
and printTypeAtom =
  fun
  | (MOLTerm(_) | MBool | MString | MTag | MTuple(_)) as t => printType(t)
  | t => "(" ++ printType(t) ++ ")";

let rec printML = (t: ml): string => {
  /* Mirrors printOL's pchild: a nested Ap with parens=false needs an
     explicit wrap, otherwise `eq A B (f x) (g y)` prints as
     `eq A B f x g y` and reads as one flat 6-arg application. */
  let pchild = (s: ml): string => {
    switch (s.value) {
    | Ap(_, _) when !s.meta.parens => "(" ++ printML(s) ++ ")"
    | _ => printML(s)
    }
  };
  let inner =
    switch (t.value) {
    | Hole => "?"
    | Meta(n) => "?M" ++ string_of_int(n)
    | TagLit(name) => "#" ++ name
    | Identifier(v) => v
    | StringLit(s) => "\"" ++ s ++ "\""
    | Tuple(items) =>
      String.concat(", ", List.map(printML, items))
    | BinOp(op, left, right) =>
      printML(left) ++ " " ++ printBinOp(op) ++ " " ++ printML(right)
    /* Infix operators encoded as Ap(Identifier(op), [l, r]) — produced
       by the catch-all in buildForm for operators like ->, =, etc. */
    | Ap({value: Identifier("->"), _}, [l, r]) =>
      printML(l) ++ " -> " ++ printML(r)
    | Ap({value: Identifier("="), _}, [l, r]) =>
      printML(l) ++ " = " ++ printML(r)
    | Ap(f, args) =>
      pchild(f) ++ " " ++ String.concat(" ", List.map(pchild, args))
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
      "let " ++ printPat(b.pat)
      ++ (switch (b.annotation) {
          | Some(ann) => " : " ++ printType(ann)
          | None => ""
          })
      ++ " = " ++ printML(b.definition)
      ++ " in " ++ printML(body)
    };
  t.meta.parens ? "(" ++ inner ++ ")" : inner;
};

let rec debugML = (t: ml): string => {
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | Hole => "Hole"
  | Meta(n) => "Meta(" ++ string_of_int(n) ++ ")"
  | Identifier(v) => "Id(" ++ v ++ ")"
  | StringLit(s) => "Str(" ++ s ++ ")"
  | TagLit(name) => "Tag(#" ++ name ++ ")"
  | Tuple(items) =>
    p ++ "Tuple(" ++ String.concat(",", List.map(debugML, items)) ++ ")"
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
    "Let(" ++ debugPat(b.pat) ++ "," ++ debugML(b.definition) ++ "," ++ debugML(body) ++ ")"
  | If(c, t, e) =>
    "If(" ++ debugML(c) ++ "," ++ debugML(t) ++ "," ++ debugML(e) ++ ")"
  };
};

/* --- Declaration and block printers ---
   We preserve the outer `parens` flag on retType/declArgType so a round-
   trip through the parser produces the same AST. Stripping would have
   the printer output `Ul` for a stored `(Ul)` (parens=true), and the
   re-parse would see a paren-less form — breaking elaboration
   idempotence whenever the parens flag carries semantic weight (e.g.
   the parenthesized-singleton constructor-elaboration trigger). */

let printDeclArg = (a: declArg): string =>
  "(" ++ a.declArgName.string ++ " : " ++ printOL(a.declArgType) ++ ")";

let printDeclLine = (d: declLine): string =>
  switch (d.args) {
  | [] => d.declName.string ++ " : " ++ printOL(d.retType)
  | args =>
    d.declName.string ++ " " ++ String.concat(" ", List.map(printDeclArg, args))
    ++ " : " ++ printOL(d.retType)
  };

let printTagLine = (t: tagLine): string =>
  "#" ++ t.tag ++ " " ++ t.target;

let printOLLine = (l: olLine): string =>
  switch (l) {
  | Decl(d) => printDeclLine(d)
  | Tag(t) => printTagLine(t)
  };

let printLetBinding = (b: letBinding): string =>
  printPat(b.pat)
  ++ (switch (b.annotation) {
      | Some(ann) => " : " ++ printType(ann)
      | None => ""
      })
  ++ " = " ++ printML(b.definition);

let printBinding = (b: binding): string =>
  b.pat
  ++ (switch (b.annotation) {
      | Some(ann) => " : " ++ printType(ann)
      | None => ""
      })
  ++ " = " ++ printML(b.definition);

let printMetaDef = (d: metaDef): string =>
  switch (d) {
  | LetDef(b) => printLetBinding(b)
  | SchemaDef(b) => "schema " ++ printBinding(b)
  | CoerceDef(b) => "coerce " ++ printBinding(b)
  | NewtagDef(tag, _) => "newtag #" ++ tag
  };

let printBlock = (b: block): string => {
  let printLines = (lines) =>
    String.concat("\n", List.map(printOLLine, lines));
  switch (b) {
  | Postulate(pb) => "postulate\n" ++ printLines(pb.lines)
  | Meta(defs) => "meta\n" ++ String.concat("\n", List.map(printMetaDef, defs))
  | Construct(cb) => "construct by " ++ cb.schema ++ "\n" ++ printLines(cb.lines)
  };
};

let printProgram = (p: program): string =>
  String.concat("\n", List.map(printBlock, p)) ++ "\n";
