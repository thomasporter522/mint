open Term;

/* Print a primary token (used by the parser/builder, not usually called directly). */
let printPrimaryToken =
  fun
  | Grammar.BOF | Grammar.EOF => ""
  | TAtom(Grammar.Hole) => "?"
  | TAtom(Identifier(v)) => v
  | TAtom(StringLit(s)) => "\"" ++ s ++ "\""
  | TNamed(n) => n;

let printBinop : binOp => string = 
  fun                                                           
    | Eq => "=="
    | Neq => "!="                                                                                      
    | And => "&&"
    | Or => "||"; 

/* Debug printer: shows AST structure. Prefix with "P" when parens=true.
   Examples:
     Identifier("x")              => "Id(x)"
     Ap(f, [x, y]) with parens    => "PAp(Id(f),[Id(x),Id(y)])"
     Hole(false)                   => "Hole"
     Hole(true)                    => "Hole_"
     Fun(pat, body)                => "Fun(Id(x),Id(x))"
     Match(s, [(p,b)])             => "Match(Id(s),[(Id(p)=>Id(b))])" */
let rec debugTerm = (t: term): string => {
  let printList = l => "[" ++ String.concat(",", l) ++ "]";
  let p = t.meta.parens ? "P" : "";
  switch (t.value) {
  | Shard(shard) => "Shard(" ++ printPrimaryToken(shard) ++ ")"
  | Hole(ht) => ht == User ? "Hole" : "Hole_"
  | Identifier(v) => "Id(" ++ v ++ ")"
  | StringLit(s) => "StringLit(" ++ s ++ ")"
  | Asc(l, r) => "Asc(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Arrow(l, r) => "Arrow(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Eq(l, r) => "Eq(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Comma(l, r) => "Comma(" ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | BinOp(op, l, r) => "Binop(" ++ printBinop(op) ++ debugTerm(l) ++ "," ++ debugTerm(r) ++ ")"
  | Ap(f, args) => "Ap(" ++ debugTerm(f) ++ "," ++ printList(List.map(debugTerm,args)) ++ ")"
  | List(items) => "Id(" ++ ++ ")"
  | Cons(heads, tail) => "Id(" ++ ++ ")"
  | Fun(pat, body) => "Id(" ++ ++ ")"
  | Match(scrut, branches) => "Id(" ++ ++ ")"
  | Let(b, body) => "Id(" ++ ++ ")"
  | If(c, t, e) => "Id(" ++ ++ ")"
  | Postulate(body, _) => "Id(" ++ ++ ")"
  | Meta(_, _) => "Id(" ++ ++ ")"
  | Construct(_, _, _) => "Id(" ++ ++ ")"
  | BuilderError => "Id(" ++ ++ ")"
  };
};

/* Pretty printer: produces readable output that round-trips through the parser.
   The key insight: if t.meta.parens is true, wrap the whole result in parens.

   Cases:
   - Hole(true) prints as "" (synthetic, invisible)
   - Hole(false) prints as "?"
   - Ap(f, args): "f a1 a2" (space-separated)
   - Asc(l, r): "l : r"
   - List(items): "[a, b, c]" (comma-separated)
   - Cons(heads, tail): "[h1, h2, ...tail]"
   - Comma(l, r): "l, r"
   - Fun(pat, body): "fun pat => body"
   - Match(scrut, branches): "match s with | p1 => b1 | p2 => b2 end"
   - If(c, t, e): "if c then t else e end"
   - Let(binding, body): "let binding in body"
   - BinOp(op, l, r): "l op r"
   - Arrow(l, r): "l -> r"
   - Eq(l, r): "l = r"
   - Postulate/Meta/Construct: block syntax with newlines and "end" */
let rec printTerm = (t: term): string => {
  let inner =
    switch (t.value) {
    | Shard(token) => printPrimaryToken(token)
    | Hole(inserted) => failwith("TODO")
    | Identifier(v) => failwith("TODO")
    | StringLit(s) => failwith("TODO")
    | Asc(left, right) => failwith("TODO")
    | Arrow(left, right) => failwith("TODO")
    | Eq(left, right) => failwith("TODO")
    | Comma(left, right) => failwith("TODO")
    | BinOp(op, left, right) => failwith("TODO")
    | Ap(f, args) => failwith("TODO")
    | List(items) => failwith("TODO")
    | Cons(heads, tail) => failwith("TODO")
    | Fun(pat, body) => failwith("TODO")
    | Match(scrut, branches) => failwith("TODO")
    | Let(binding, body) => failwith("TODO")
    | If(cond, thenBr, elseBr) => failwith("TODO")
    | Postulate(body, rest) => failwith("TODO")
    | Meta(body, rest) => failwith("TODO")
    | Construct(by, body, rest) => failwith("TODO")
    | BuilderError => "<BUILDER ERROR>"
    };
  /* Wrap in parens if the meta flag says so */
  failwith("TODO: use t.meta.parens");
};
