
type ghostKind =
  | Implicit
  | Coerce;

type meta = {
  parens: bool,
  start: int,
  end_: int,
  ghost: option(ghostKind),
};

type stringMeta = {
  string : string, 
  meta : meta
}

type cOL =
  | OLHole
  | OLAp(stringMeta, list(ol))
  | OLMeta(int)
and ol = {
  value: cOL,
  meta,
};

type declArg = {
  declArgName: stringMeta,
  declArgType: ol,
  declArgMeta: meta,
};

type declLine = {
  declName: stringMeta,
  args: list(declArg),
  retType: ol,
  declMeta: meta,
};

type tagLine = {
  tag: string,
  target: string,
  lineMeta: meta,
};

type olLine = 
  | Decl(declLine)
  | Tag(tagLine)

type mlType =
  | MOLTerm(ol)
  | MBool
  | MString
  | MTag
  | MList(mlType)
  | MResult(mlType)
  | MTuple(list(mlType))
  | MArrow(mlType, mlType)

type cPat =
  | PWildcard
  | PVar(string)
  | PString(string)
  | PList(list(pat))
  | PCons(pat, pat)
  | PTuple(list(pat))
  | POLAp(string, list(pat))
and pat = {
  value: cPat,
  meta,
};

type binOp =
  | Eq
  | Neq
  | And
  | Or

type cML =
  | Hole
  | Meta(int)
  | Identifier(string) // could be OL or ML
  | Ap(ml, list(ml)) // could be OL or ML
  | StringLit(string)
  | TagLit(string)
  | Tuple(list(ml))
  // | Asc(ml, ml)
  | BinOp(binOp, ml, ml)
  | List(list(ml))
  | Cons(ml, ml)
  | Fun(list(pat), ml)
  | Match(ml, list((pat, ml)))
  | If(ml, ml, ml)
  | Let(letBinding, ml)
and ml = {
  value: cML,
  meta,
}

/* let [pat] : [annotation] = [definition] */
and letBinding = {
  pat: pat,
  annotation: option(mlType),
  // rawAnnotation: option(ml),          /* raw type expression, preserved for error reporting */
  definition: ml,
  bindingMeta: meta,
};

type binding = {
  pat: string,
  annotation: option(mlType),
  definition: ml,
  bindingMeta: meta,
};

type metaDef =
  | LetDef(letBinding)
  | SchemaDef(binding)
  | CoerceDef(binding)
  /* `newtag #foo` — introduces the tag #foo into the tag namespace. */
  | NewtagDef(string, meta)

type postulateBlock = {
  postulateMeta : meta, 
  lines : list(olLine)
}

type constructBlock = {
  schema : string, 
  schemaMeta : meta, 
  lines : list(olLine)
}

type block =
  | Postulate(postulateBlock)
  | Meta(list(metaDef))
  | Construct(constructBlock)

type program = list(block);

// Helpers

let defaultMeta = {parens: false, start: (-1), end_: (-1), ghost: None};

/* Mark any subterm as ghost with the given kind. */
let asGhost = (k: ghostKind, m: meta): meta => {...m, ghost: Some(k)};

/* Predicate convenience — most call sites just ask "is this synthesized?" */
let isGhost = (m: meta): bool =>
  switch (m.ghost) {
  | Some(_) => true
  | None => false
  };

let mkOL = (t: cOL): ol => {value: t, meta: defaultMeta};
let mkML = (t: cML): ml => {value: t, meta: defaultMeta};
let mkPat = (p: cPat): pat => {value: p, meta: defaultMeta};

let rec embedOL = (t: ol): ml => {
  let value =
    switch (t.value) {
    | OLHole => Hole
    | OLMeta(n) => Meta(n)
    | OLAp(f, args) => 
      let mlF = {
        value: Identifier(f.string),
        meta: f.meta
      }
      Ap(mlF, List.map(embedOL, args))
    };
  {value, meta: t.meta};
};
