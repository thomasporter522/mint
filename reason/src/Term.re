/* What kind of ghost a synthesized subterm is. Inlay-hint extraction
   walks the elaborated AST and renders each ghost subtree according to
   its kind:
     Implicit — an arg slot the elaborator filled in (e.g. the missing
       universe args of `(ap f a)`). Maximal leading runs of these
       inside an Ap collapse to a single `…` anchored at the head's end.
     Coerce — a synthesized wrapping inserted around a user subterm.
       The whole wrapping subtree is Coerce-ghost; the user's subject
       sits inside it as non-ghost. Renders as `°` at the subject with
       the wrapping as the hover tooltip.
   Holding the ghost classification in the term itself means there is
   no parallel diagnostic side table: hints and "not fully solved"
   warnings are pure functions of the final elaborated term. */
type ghostKind =
  | Implicit
  | Coerce;

type meta = {
  parens: bool,
  start: int,
  end_: int,
  ghost: option(ghostKind),
};

/* --- Small enums --- */

type holeKind =
  | User        /* ? written in source */
  | Synthesized /* inserted by the builder */
  | Auto        /* ⟐ — request a Canonical solver invocation */

type binOp =
  | Eq
  | Neq
  | And
  | Or

/* === Object language === */

/* OL terms: the language inside declarations. Just identifiers,
   application, holes, and metavariables. Metas are introduced by the
   elaborator when the user underapplies a constructor; they're never
   parsed from source. The integer is a per-declaration unique ID. */
type cOL =
  | OLHole(holeKind)
  | OLIdentifier(string)
  | OLAp(ol, list(ol))                      /* f x y z */
  | OLMeta(int)
and ol = {
  value: cOL,
  meta,
};

/* OL declarations: name, typed parameters, return type */
type param = {
  paramName: string,
  paramType: ol,
  paramMeta: meta,
  /* Range of the param's name identifier alone, used as the
     go-to-definition target. */
  nameMeta: meta,
};

type decl = {
  declName: string,
  params: list(param),
  retType: ol,
  declMeta: meta,
  /* Range of the name identifier itself — narrower than declMeta. Used
     as the go-to-definition target so a self-reference like the second
     `Sort` in `Sort : Sort` navigates to the first `Sort` rather than
     to a range that already contains the click. */
  nameMeta: meta,
};

/* === Meta language === */

/* ML types — the type language of the meta-language.
   Parsed from annotation syntax by the builder. */
type mlType =
  | MTerm
  | MBool
  | MString
  | MTag                                     /* `#name` tag value */
  | MList(mlType)
  | MResult(mlType)
  | MTuple(list(mlType))                     /* (A, B, C) — arbitrary arity */
  | MArrow(mlType, mlType)                   /* A -> B */

/* ML patterns */
type cPat =
  | PWildcard                                /* _ */
  | PVar(string)                             /* x */
  | PHole                                    /* ? in pattern position */
  | PString(string)                          /* "literal" */
  | PList(list(pat))                         /* [p1, p2, p3] */
  | PCons(pat, pat)                          /* p :: ptail */
  | PTuple(list(pat))                        /* (p1, p2, p3) */
  | PAp(pat, list(pat))                       /* (f p1 p2) — head + arg patterns */
and pat = {
  value: cPat,
  meta,
};

/* ML expressions: the meta-language. Has its own Identifier and Ap
   that mirror the OL constructors but take ml subterms, since ML
   expressions can mix OL identifiers with ML-bound variables. */
type cML =
  | Hole(holeKind)
  | Identifier(string)                        /* x — could be OL or ML, resolved by checker */
  | StringLit(string)
  | TagLit(string)                            /* #name — tag-value literal */
  | Tuple(list(ml))                          /* (a, b, c) */
  | Asc(ml, ml)                              /* x : T — ascription (mostly syntactic) */
  | BinOp(binOp, ml, ml)                     /* a == b, a && b, etc. */
  | Ap(ml, list(ml))                         /* f x y — could be OL or ML application */
  | List(list(ml))                           /* [a, b, c] */
  | Cons(ml, ml)                             /* h :: t */
  | Fun(list(pat), ml)                       /* fun p1 p2 => body */
  | Match(ml, list((pat, ml)))               /* match scrut with | p => e end */
  | If(ml, ml, ml)                           /* if cond then t else e end */
  | Let(binding, ml)                         /* let name : T = e in body */
and ml = {
  value: cML,
  meta,
}

/* ML bindings (shared by let and meta-level definitions).
   `pat` is the LHS pattern; for top-level meta defs (LetDef/SchemaDef/
   CoerceDef) and most let-ins it is just `PVar(name)`, but Let admits
   arbitrary patterns so `let (a, b) = e in …` destructures. */
and binding = {
  pat: pat,
  annotation: option(mlType),         /* parsed directly into mlType by the builder */
  rawAnnotation: option(ml),          /* raw type expression, preserved for error reporting */
  rhs: ml,
  bindingMeta: meta,
};

/* Meta-level definitions */
type metaDef =
  | LetDef(binding)                          /* name (: type) = body */
  | SchemaDef(binding)                       /* schema name (: type) = body */
  | CoerceDef(binding)                       /* coerce name (: type) = body */
  /* `newtag #foo` — introduces the tag #foo into the tag namespace. */
  | NewtagDef(string, meta)

/* `#tag constructor` decoration in a postulate/construct block. Doesn't
   introduce a name; records that `target` carries `tag`. */
type tagLine = {
  tag: string,
  target: string,
  lineMeta: meta,
};

/* === Program structure === */

type block =
  /* Postulate(blockMeta, decls, tagLines) — blockMeta is the full source
     range of the block (from the `postulate` keyword to the last decl).
     Used to anchor the per-block completeness ✓ and to filter against
     errors. tagLines decorate already-declared bindings. */
  | Postulate(meta, list(decl), list(tagLine))
  | Meta(list(metaDef))
  /* Construct(schemaName, schemaMeta, blockMeta, decls, tagLines) —
     schemaMeta localizes schema-related errors; blockMeta is the full
     block range. */
  | Construct(string, meta, meta, list(decl), list(tagLine))

type program = list(block);

/* === Helpers === */

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

/* For places that historically referred to a binding's name (top-level
   meta defs, LetDef, SchemaDef, CoerceDef): the LHS pattern is always
   a PVar there, so extracting the name is safe. Returns "_" if the
   binding was somehow destructuring at a position that expected a
   single name — those positions only arise through grammar rules that
   restrict the LHS to an Identifier, so this is defensive. */
let bindingName = (b: binding): string =>
  switch (b.pat.value) {
  | PVar(n) => n
  | _ => "_"
  };

/* Embed an OL term into the ML language, preserving structure and metadata.
   An unsolved meta degrades to Hole(User) so it prints as `?` in goal
   tooltips — Hole(Synthesized) would print as empty (parser-fallback
   convention) and turn `Ul ?M` into the misleading `Ul`. */
let rec embedOL = (t: ol): ml => {
  let value =
    switch (t.value) {
    | OLHole(k) => Hole(k)
    | OLMeta(_) => Hole(User)
    | OLIdentifier(s) => Identifier(s)
    | OLAp(f, args) => Ap(embedOL(f), List.map(embedOL, args))
    };
  {value, meta: t.meta};
};
