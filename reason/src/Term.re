type meta = {
  parens: bool,
  start: int,
  end_: int,
};

/* --- Small enums --- */

type holeKind =
  | User        /* ? written in source */
  | Synthesized /* inserted by the builder */

type binOp =
  | Eq
  | Neq
  | And
  | Or

/* === Object language === */

/* OL terms: the language inside declarations. Just identifiers,
   application, and holes. No lambdas, no lists, no matching. */
type cOL =
  | OLHole(holeKind)
  | OLIdentifier(string)
  | OLAp(ol, list(ol))                      /* f x y z */
and ol = {
  value: cOL,
  meta,
};

/* OL declarations: name, typed parameters, return type */
type param = {
  paramName: string,
  paramType: ol,
  paramMeta: meta,
};

type decl = {
  declName: string,
  params: list(param),
  retType: ol,
  declMeta: meta,
};

/* === Meta language === */

/* ML patterns */
type cPat =
  | PWildcard                                /* _ */
  | PVar(string)                             /* x */
  | PHole                                    /* ? in pattern position */
  | PString(string)                          /* "literal" */
  | PList(list(pat))                         /* [p1, p2, p3] */
  | PCons(pat, pat)                          /* p :: ptail */
  | PTuple(list(pat))                        /* (p1, p2, p3) */
  | PAp(string, list(pat))                    /* (C p1 p2) — constructor name + arg patterns */
and pat = {
  value: cPat,
  meta,
};

/* ML expressions: the meta-language. Has its own Identifier and Ap
   that mirror the OL constructors but take ml subterms, since ML
   expressions can mix OL identifiers with ML-bound variables. */
type cML =
  | Shard(Grammar.primaryToken)              /* parse artifact */
  | Hole(holeKind)
  | Identifier(string)                       /* x — could be OL or ML, resolved by checker */
  | StringLit(string)
  | Tuple(list(ml))                          /* (a, b, c) */
  | BinOp(binOp, ml, ml)                     /* a == b, a && b, etc. */
  | Ap(ml, list(ml))                         /* f x y — could be OL or ML application */
  | List(list(ml))                           /* [a, b, c] */
  | Cons(ml, ml)                             /* h :: t */
  | Fun(list(pat), ml)                       /* fun p1 p2 => body */
  | Match(ml, list((pat, ml)))               /* match scrut with | p => e end */
  | If(ml, ml, ml)                           /* if cond then t else e end */
  | Let(binding, ml)                         /* let name : T = e in body */
  | BuilderError                             /* parse artifact */
and ml = {
  value: cML,
  meta,
}

/* ML bindings (shared by let and meta-level definitions) */
and binding = {
  name: string,
  annotation: option(ml),      /* : type (parsed as ML, converted to mlType) */
  rhs: ml,
  bindingMeta: meta,
};

/* Meta-level definitions */
type metaDef =
  | LetDef(binding)                          /* name (: type) = body */
  | SchemaDef(binding)                       /* schema name (: type) = body */

/* === Program structure === */

type block =
  | Postulate(list(decl))
  | Meta(list(metaDef))
  | Construct(string, list(decl))            /* schema name, declarations */

type program = list(block);

/* === Helpers === */

let defaultMeta = {parens: false, start: (-1), end_: (-1)};

let mkOL = (t: cOL): ol => {value: t, meta: defaultMeta};
let mkML = (t: cML): ml => {value: t, meta: defaultMeta};
let mkPat = (p: cPat): pat => {value: p, meta: defaultMeta};

/* Embed an OL term into the ML language, preserving structure and metadata. */
let rec embedOL = (t: ol): ml => {
  let value =
    switch (t.value) {
    | OLHole(k) => Hole(k)
    | OLIdentifier(s) => Identifier(s)
    | OLAp(f, args) => Ap(embedOL(f), List.map(embedOL, args))
    };
  {value, meta: t.meta};
};
