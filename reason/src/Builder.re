open Utils;
open Grammar;
open Term;
open Parser;

/* === Helpers === */

let mk = mkML;

let combineTerms =
  fun
  | [] => mk(Hole(Synthesized))
  | [t] => t
  | [first, ..._] as ts => {
      let last = List.nth(ts, List.length(ts) - 1);
      let t = mk(Ap(first, List.tl(ts)));
      {...t, meta: {...t.meta, start: first.meta.start, end_: last.meta.end_}};
    };

let localize = (t: ml, token: ranged(primaryToken)): ml =>
  {...t, meta: {...t.meta, start: token.start, end_: token.end_}};

let localizePat = (p: pat, token: ranged(primaryToken)): pat =>
  {...p, meta: {...p.meta, start: token.start, end_: token.end_}};

let isCommaToken = (tok: primaryToken): bool =>
  switch (tok) {
  | TNamed("," | ",p" | ",l") => true
  | _ => false
  };

let metaFromRange = (start, end_): meta =>
  {parens: false, start, end_};

/* (nameFromItems moved into the and-chain below) */

/* === mlType conversion from intermediate ml expressions === */

let rec mlToType = (t: ml): option(mlType) =>
  switch (t.value) {
  | Identifier("Term") => Some(MTerm)
  | Identifier("Sort") => Some(MSort)
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Signature") =>
    Some(MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm]))
  | Ap({value: Identifier("List"), _}, [arg]) =>
    switch (mlToType(arg)) {
    | Some(t) => Some(MList(t))
    | None => None
    }
  | Ap({value: Identifier("Result"), _}, [arg]) =>
    switch (mlToType(arg)) {
    | Some(t) => Some(MResult(t))
    | None => None
    }
  | Ap({value: Identifier("->"), _}, [l, r]) =>
    switch (mlToType(l), mlToType(r)) {
    | (Some(lt), Some(rt)) => Some(MArrow(lt, rt))
    | _ => None
    }
  | Tuple(items) =>
    let types = List.map(mlToType, items);
    if (List.for_all(t => t != None, types)) {
      Some(MTuple(List.map(t => switch (t) { | Some(v) => v | None => MTerm }, types)))
    } else {
      None
    }
  | _ => None
  };

/* === Pattern building === */

let rec buildPat = (form: openForm): pat => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* Bracket forms: (...), [...] */
  | (None, [], CMatch(_, _, {value: TNamed(")" | "]"), _}), [], None) =>
    let (open_, elementGroups) = collectBracketElements(closed);
    let elements = List.map(buildPatTerms, elementGroups);
    switch (open_, elements) {
    | ("(", [single]) => {...single, meta: {...single.meta, parens: true}}
    | ("(", elements) =>
      let p = mkPat(PTuple(elements));
      {...p, meta: {...p.meta, parens: true}}
    | ("[", items) =>
      switch (List.rev(items)) {
      | [{value: PHole, _}] =>
        /* [] with nothing inside — empty list */
        mkPat(PList([]))
      | _ => mkPat(PList(items))
      }
    | _ => mkPat(PWildcard)
    };

  /* Infix :: in patterns */
  | (_, _, CHead({value: TNamed("::"), _} as tok), _, _) =>
    let headPat = buildPatLeftChild(left, leftUf);
    let tailPat = buildPatChild(rightUf, right);
    localizePat(mkPat(PCons(headPat, tailPat)), tok)

  /* Atoms */
  | (None, [], CHead({value: TAtom(Hole), _} as tok), [], None) =>
    localizePat(mkPat(PHole), tok)
  | (None, [], CHead({value: TAtom(Identifier("_")), _} as tok), [], None) =>
    localizePat(mkPat(PWildcard), tok)
  | (None, [], CHead({value: TAtom(Identifier(v)), _} as tok), [], None) =>
    localizePat(mkPat(PVar(v)), tok)
  | (None, [], CHead({value: TAtom(StringLit(s)), _} as tok), [], None) =>
    localizePat(mkPat(PString(s)), tok)

  /* _ keyword */
  | (None, [], CHead({value: TNamed("_"), _} as tok), [], None) =>
    localizePat(mkPat(PWildcard), tok)

  /* Named token as pattern variable */
  | (None, [], CHead({value: TNamed(name), _} as tok), [], None) =>
    localizePat(mkPat(PVar(name)), tok)

  | _ => mkPat(PWildcard)
  };
}

and buildPatTerms = (fs: list(sharded(openForm))): pat =>
  combinePatTerms(List.concat_map(buildPatSharded, fs))

and combinePatTerms = (ps: list(pat)): pat =>
  switch (ps) {
  | [] => mkPat(PHole)
  | [p] => p
  | [head, ...args] when List.length(args) > 0 =>
    let first = List.hd(args);
    let last = List.nth(args, List.length(args) - 1);
    let p = mkPat(PAp(head, args));
    {...p, meta: metaFromRange(first.meta.start, last.meta.end_)};
  | [p, ..._] => p
  }

and buildPatChild = (unforms, form) =>
  combinePatTerms(
    switch (form) {
    | Some(f) => buildPatUnforms(unforms) @ [buildPat(f)]
    | None => buildPatUnforms(unforms)
    },
  )

and buildPatLeftChild = (left, leftUf) =>
  combinePatTerms(
    switch (left) {
    | Some(f) => [buildPat(f), ...buildPatUnforms(leftUf)]
    | None => buildPatUnforms(leftUf)
    },
  )

and buildPatUnform =
  fun
  | USecondary(_) => []
  | UShard(_) => []

and buildPatUnforms = unforms => List.concat_map(buildPatUnform, unforms)

and buildPatSharded =
  fun
  | Unform(u) => buildPatUnform(u)
  | Form(f) => [buildPat(f)]

/* === Bracket element collection (shared by ml and pat building) === */

and collectBracketElements = (cf: closedForm): (string, list(list(sharded(openForm)))) =>
  switch (cf) {
  | CHead({value: TNamed(open_), _}) => (open_, [])
  | CMatch(inner, items, {value, _}) when isCommaToken(value) || value == TNamed(")") || value == TNamed("]") || value == TNamed(":p") =>
    let (open_, prev) = collectBracketElements(inner);
    (open_, prev @ [items])
  | _ => ("", [])
  }

/* Extract an identifier name from parse tree items */
and nameFromItems = (items: list(sharded(openForm))): string => {
  let t = buildTerms(items);
  switch (t.value) {
  | Identifier(name) => name
  | _ => "_"
  };
}

/* === Block-level builders === */

/* Build an OL term from an openForm. OL terms are identifiers,
   application, and holes — any ML construct produces OLHole as error recovery. */
and buildOLTerm = (form: openForm): ol => {
  let {left, leftUf: _, closed, rightUf: _, right} = form;

  switch (left, closed, right) {
  /* Atom: identifier */
  | (None, CHead({value: TAtom(Identifier(v)), _} as tok), None) =>
    {value: OLIdentifier(v), meta: metaFromRange(tok.start, tok.end_)}
  /* Atom: hole */
  | (None, CHead({value: TAtom(Hole), _} as tok), None) =>
    {value: OLHole(User), meta: metaFromRange(tok.start, tok.end_)}
  /* Named token as identifier (e.g. Sort) */
  | (None, CHead({value: TNamed(name), _} as tok), None) =>
    {value: OLIdentifier(name), meta: metaFromRange(tok.start, tok.end_)}
  /* Parens: (...) — just recurse, preserving parens flag */
  | (None, CMatch(_, _, {value: TNamed(")"), _}), None) =>
    let (_, elementGroups) = collectBracketElements(closed);
    switch (elementGroups) {
    | [single] =>
      let inner = buildOLTerms(single);
      {...inner, meta: {...inner.meta, parens: true}}
    | _ => mkOL(OLHole(Synthesized))
    }
  /* Application: left + head + right form an OLAp */
  | (_, _, _) =>
    let parts = buildOLLeftChild(form.left, form.leftUf)
      @ [buildOLHead(closed)]
      @ buildOLRightChild(form.rightUf, form.right);
    combineOLTerms(parts)
  };
}

and buildOLHead = (cf: closedForm): ol =>
  switch (cf) {
  | CHead({value: TAtom(Identifier(v)), _} as tok) =>
    {value: OLIdentifier(v), meta: metaFromRange(tok.start, tok.end_)}
  | CHead({value: TAtom(Hole), _} as tok) =>
    {value: OLHole(User), meta: metaFromRange(tok.start, tok.end_)}
  | CHead({value: TNamed(name), _} as tok) =>
    {value: OLIdentifier(name), meta: metaFromRange(tok.start, tok.end_)}
  | CMatch(_, _, {value: TNamed(")"), _}) =>
    let (_, elementGroups) = collectBracketElements(cf);
    switch (elementGroups) {
    | [single] =>
      let inner = buildOLTerms(single);
      {...inner, meta: {...inner.meta, parens: true}}
    | _ => mkOL(OLHole(Synthesized))
    }
  | _ => mkOL(OLHole(Synthesized))
  }

and buildOLLeftChild = (left, leftUf) =>
  switch (left) {
  | Some(f) => [buildOLTerm(f), ...buildOLUnforms(leftUf)]
  | None => buildOLUnforms(leftUf)
  }

and buildOLRightChild = (rightUf, right) =>
  switch (right) {
  | Some(f) => buildOLUnforms(rightUf) @ [buildOLTerm(f)]
  | None => buildOLUnforms(rightUf)
  }

and buildOLUnforms = (unforms): list(ol) =>
  List.concat_map(
    fun
    | USecondary(_) => []
    | UShard(_) => [],
    unforms,
  )

and buildOLSharded =
  fun
  | Unform(_) => []
  | Form(f) => [buildOLTerm(f)]

/* Combine multiple OL items as OLAp (like combineTerms but for OL) */
and combineOLTerms =
  fun
  | [] => mkOL(OLHole(Synthesized))
  | [t] => t
  | [first, ...rest] => {
      let last = List.nth(rest, List.length(rest) - 1);
      {value: OLAp(first, rest), meta: metaFromRange(first.meta.start, last.meta.end_)};
    }

/* Build OL terms from sharded items — like buildTerms but for OL */
and buildOLTerms = (items: list(sharded(openForm))): ol =>
  combineOLTerms(List.concat_map(buildOLSharded, items))

/* Build a param from a closedForm that has the :p structure.
   (name :p type) → CMatch(CMatch(CHead("("), nameItems, ":p"), typeItems, ")") */
and buildParam = (cf: closedForm): param =>
  switch (cf) {
  | CMatch(CMatch(CHead({value: TNamed("("), _}), nameItems, {value: TNamed(":p"), _}), typeItems, {value: TNamed(")"), _}) =>
    let name = nameFromItems(nameItems);
    let paramType = buildOLTerms(typeItems);
    {paramName: name, paramType, paramMeta: defaultMeta}
  | _ =>
    {paramName: "_", paramType: mkOL(OLHole(Synthesized)), paramMeta: defaultMeta}
  }

/* Build a decl directly from an openForm.
   Declarations are either:
   - name : retType  (: as infix)
   - (name params...) : retType  (: as infix, lhs is paren group)
   - bare name  (no colon, for construct blocks) */
and buildDeclFromForm = (form: openForm): decl => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (closed) {
  /* Infix : — this is a declaration with type annotation */
  | CHead({value: TNamed(":"), _}) =>
    let lhs = buildLeftChild(left, leftUf);
    let retType = buildOLChild(rightUf, right);
    switch (lhs.value) {
    /* name : retType — no params */
    | Identifier(name) =>
      {declName: name, params: [], retType, declMeta: form |> formMeta}
    /* (name params...) : retType — with params */
    | Ap({value: Identifier(name), _}, paramExprs) when lhs.meta.parens =>
      let params = List.map(extractParamFromML, paramExprs);
      {declName: name, params, retType, declMeta: form |> formMeta}
    | _ =>
      {declName: "_", params: [], retType, declMeta: form |> formMeta}
    }

  /* Bare identifier — no colon */
  | CHead({value: TAtom(Identifier(name)), _}) when left == None && right == None =>
    {declName: name, params: [], retType: mkOL(OLHole(Synthesized)), declMeta: form |> formMeta}

  /* Fallback */
  | _ =>
    {declName: "_", params: [], retType: mkOL(OLHole(Synthesized)), declMeta: form |> formMeta}
  };
}

/* Extract an OL term from the right child of an openForm */
and buildOLChild = (rightUf, right): ol =>
  switch (right) {
  | Some(f) =>
    let ufs = buildOLUnforms(rightUf);
    combineOLTerms(ufs @ [buildOLTerm(f)])
  | None =>
    combineOLTerms(buildOLUnforms(rightUf))
  }

/* Compute meta for a form from its children */
and formMeta = (form: openForm): meta => {
  /* Use buildLeftChild/buildChild to get position info, or default */
  let start = switch (form.left) {
  | Some(f) => (buildForm(f)).meta.start
  | None => switch (form.closed) {
    | CHead(tok) => tok.start
    | CMatch(_, _, tok) => tok.start
    }
  };
  let end_ = switch (form.right) {
  | Some(f) => (buildForm(f)).meta.end_
  | None => switch (form.closed) {
    | CHead(tok) => tok.end_
    | CMatch(_, _, tok) => tok.end_
    }
  };
  {parens: false, start, end_};
}

/* Extract a param from an ML expression (used when lhs of : is a paren group
   that was built via buildLeftChild, which goes through buildForm).
   The ML Ap(Identifier(":"), [name, type]) inside a parens group = a param. */
and extractParamFromML = (t: ml): param =>
  switch (t.value) {
  | Tuple([{value: Identifier(name), _}, typeExpr]) =>
    {paramName: name, paramType: mlToOL(typeExpr), paramMeta: t.meta}
  | Identifier(name) =>
    {paramName: name, paramType: mkOL(OLHole(Synthesized)), paramMeta: t.meta}
  | _ =>
    {paramName: "_", paramType: mkOL(OLHole(Synthesized)), paramMeta: t.meta}
  }

/* Build a decl from a sharded item */
and buildDeclFromSharded = (item: sharded(openForm)): option(decl) =>
  switch (item) {
  | Form(f) => Some(buildDeclFromForm(f))
  | Unform(_) => None
  }

/* Scan meta block items for definitions.
   schema keyword + definition → SchemaDef
   name = rhs → LetDef (bare)
   name : type = rhs → LetDef (annotated) */
and buildMetaDefItems = (items: list(sharded(openForm))): list(metaDef) =>
  scanMetaSharded(items)

and scanMetaSharded = (items: list(sharded(openForm))): list(metaDef) =>
  switch (items) {
  | [] => []
  /* schema keyword followed by a form → SchemaDef */
  | [Form({left: None, leftUf: [], closed: CHead({value: TAtom(Identifier("schema")) | TNamed("schema"), _}), rightUf: [], right: None}), Form(defForm), ...rest] =>
    [SchemaDef(buildBindingFromForm(defForm)), ...scanMetaSharded(rest)]
  /* Regular form → LetDef */
  | [Form(f), ...rest] =>
    [buildMetaDefFromForm(f), ...scanMetaSharded(rest)]
  /* Skip unforms */
  | [Unform(_), ...rest] =>
    scanMetaSharded(rest)
  }

/* Build a metaDef from an openForm (non-schema item in meta block) */
and buildMetaDefFromForm = (form: openForm): metaDef =>
  LetDef(buildBindingFromForm(form))

/* Build a binding from an openForm that has = as infix, possibly with : annotation.
   Patterns:
   - name = rhs → bare binding
   - name : type = rhs → annotated binding (the = has : infix on its left) */
and buildBindingFromForm = (form: openForm): binding => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (closed) {
  /* = as infix */
  | CHead({value: TNamed("="), _}) =>
    let lhs = buildLeftChild(left, leftUf);
    let rhs = buildChild(rightUf, right);
    switch (lhs.value) {
    /* name : type = rhs — annotated */
    | Ap({value: Identifier(":"), _}, [{value: Identifier(name), _}, typeExpr]) =>
      let annotation = mlToType(typeExpr);
      {name, annotation, rawAnnotation: Some(typeExpr), rhs, bindingMeta: defaultMeta}
    /* name = rhs — bare */
    | Identifier(name) =>
      {name, annotation: None, rawAnnotation: None, rhs, bindingMeta: defaultMeta}
    | _ =>
      {name: "_", annotation: None, rawAnnotation: None, rhs: lhs, bindingMeta: defaultMeta}
    }
  /* Fallback — not an = form, treat the whole thing as rhs */
  | _ =>
    let t = buildForm(form);
    {name: "_", annotation: None, rawAnnotation: None, rhs: t, bindingMeta: defaultMeta}
  };
}

/* Build a block value from a keyword, contents, and optional rest.
   Produces block values directly — no __postulate/__meta/__construct encoding. */
and buildBlockFromForm = (keyword: string, contents: list(sharded(openForm))): block =>
  switch (keyword) {
  | "postulate" =>
    let decls = List.filter_map(buildDeclFromSharded, contents);
    Postulate(decls)
  | "meta" =>
    let defs = buildMetaDefItems(contents);
    Meta(defs)
  | "construct" | "by" =>
    /* For construct: first item is the schema name (from `by`), rest are decls.
       For by: contents already include name + decls. */
    switch (contents) {
    | [Form({left: None, leftUf: [], closed: CHead({value: TAtom(Identifier(name)), _}), rightUf: [], right: None}), ...declItems]
    | [Form({left: None, leftUf: [], closed: CHead({value: TNamed(name), _}), rightUf: [], right: None}), ...declItems] =>
      let decls = List.filter_map(buildDeclFromSharded, declItems);
      Construct(name, decls)
    | _ =>
      Construct("_", List.filter_map(buildDeclFromSharded, contents))
    }
  | _ => Postulate([])
  }

/* Walk the CMatch structure to collect blocks for a program.
   Similar to buildBlocks but produces block values. */
and collectBlocks = (form: closedForm, contents: list(sharded(openForm))): list(block) =>
  switch (form) {
  | CHead({value: TNamed(keyword), _}) =>
    [buildBlockFromForm(keyword, contents)]
  | CMatch(inner, innerItems, {value: TNamed(keyword), _}) =>
    collectBlocks(inner, innerItems) @ [buildBlockFromForm(keyword, contents)]
  | _ => []
  }

/* Top-level entry point: walk the forms and produce a program (list of blocks). */
and buildProgram = (forms: list(sharded(openForm))): program => {
  /* At the top level, the forms should contain block structures terminated by end.
     The structure is: CMatch(blockChain, lastBlockContents, "end") */
  let blocks = List.concat_map(
    fun
    | Form(form) =>
      switch (form.closed) {
      | CMatch(inner, innerItems, {value: TNamed("end"), _}) =>
        collectBlocks(inner, innerItems)
      | _ => []
      }
    | Unform(_) => [],
    forms,
  );
  blocks;
}

/* === Main expression builder === */

and buildTerms = (fs: list(sharded(openForm))): ml =>
  combineTerms(List.concat_map(buildSharded, fs))

and buildChild = (unforms, form) =>
  combineTerms(
    switch (form) {
    | Some(f) => buildUnforms(unforms) @ [buildForm(f)]
    | None => buildUnforms(unforms)
    },
  )

and buildLeftChild = (left, leftUf) =>
  combineTerms(
    switch (left) {
    | Some(f) => [buildForm(f), ...buildUnforms(leftUf)]
    | None => buildUnforms(leftUf)
    },
  )

and buildItems = (items: list(sharded(openForm))): list(ml) =>
  List.filter_map(
    fun
    | Unform(_) => None
    | Form(f) => Some(buildForm(f)),
    items,
  )

/* --- Match chain: match(scrut)with()|(pat)=>(body)|(pat)=>(body)end --- */

and isMatchChain = (cf: closedForm): bool =>
  switch (cf) {
  | CMatch(inner, _, {value: TNamed("end" | "=>" | "|" | "with"), _}) =>
    isMatchChain(inner)
  | CHead({value: TNamed("match"), _}) => true
  | _ => false
  }

and collectMatchBranches = (cf: closedForm): (ml, list((pat, ml))) =>
  switch (cf) {
  | CMatch(CHead({value: TNamed("match"), _}), scrutItems, {value: TNamed("with"), _}) =>
    (buildTerms(scrutItems), [])
  | CMatch(inner, bodyItems, {value: TNamed("end" | "|"), _}) =>
    let body = buildTerms(bodyItems);
    switch (inner) {
    | CMatch(deeper, patItems, {value: TNamed("=>"), _}) =>
      let patForm = buildPatTerms(patItems);
      let (scrutinee, prevBranches) = collectMatchBranches(deeper);
      (scrutinee, prevBranches @ [(patForm, body)])
    | _ =>
      collectMatchBranches(inner)
    }
  | _ => (mk(Hole(Synthesized)), [])
  }

and buildMatchChain = (cf: closedForm): ml => {
  let (scrutinee, branches) = collectMatchBranches(cf);
  mk(Match(scrutinee, branches));
}

/* --- If chain: if(cond)then(thenBr)else(elseBr)end --- */

and isIfChain = (cf: closedForm): bool =>
  switch (cf) {
  | CMatch(inner, _, {value: TNamed("end" | "else" | "then"), _}) =>
    isIfChain(inner)
  | CHead({value: TNamed("if"), _}) => true
  | _ => false
  }

and buildIfChain = (cf: closedForm): ml =>
  switch (cf) {
  | CMatch(CMatch(CMatch(CHead({value: TNamed("if"), _}), condItems, {value: TNamed("then"), _}), thenItems, {value: TNamed("else"), _}), elseItems, {value: TNamed("end"), _}) =>
    mk(If(buildTerms(condItems), buildTerms(thenItems), buildTerms(elseItems)))
  | _ => mk(BuilderError)
  }

/* --- Fun handler: fun(pats)=>f(body) --- */

and buildFunPats = (items: list(sharded(openForm))): list(pat) =>
  List.filter_map(
    fun
    | Unform(_) => None
    | Form(f) => Some(buildPat(f)),
    items,
  )

/* --- Let handler: let(binding)in(body) --- */
/* The binding content is something like `name = rhs` or `name : type = rhs`.
   After buildTerms, this becomes:
   - Ap(Identifier("="), [Identifier(name), rhs])
   - Ap(Identifier("="), [Ap(Identifier(":"), [Identifier(name), typeExpr]), rhs])
*/

and parseBinding = (content: ml): binding => {
  switch (content.value) {
  /* name : type = rhs */
  | Ap({value: Identifier("="), _}, [
      {value: Ap({value: Identifier(":"), _}, [
        {value: Identifier(name), _},
        typeExpr,
      ]), _},
      rhs,
    ]) =>
    {name, annotation: mlToType(typeExpr), rawAnnotation: Some(typeExpr), rhs, bindingMeta: content.meta}
  /* name = rhs */
  | Ap({value: Identifier("="), _}, [{value: Identifier(name), _}, rhs]) =>
    {name, annotation: None, rawAnnotation: None, rhs, bindingMeta: content.meta}
  /* Fallback — couldn't parse binding */
  | _ =>
    {name: "_", annotation: None, rawAnnotation: None, rhs: content, bindingMeta: content.meta}
  };
}

/* --- Block builders --- */

and faceToken = (form: closedForm): string =>
  switch (form) {
  | CMatch(_, _, {value: TNamed(n), _}) => n
  | CHead({value: TNamed(n), _}) => n
  | _ => ""
  }

/* Scan meta block items for schema keyword + binding pairs.
   `schema` is an atom keyword, so `schema foo = body` produces
   two items: [Identifier("schema"), Ap(Identifier("="), [Identifier("foo"), body])].
   We need to combine them into a single SchemaDef. */
and scanMetaDefs = (items: list(ml)): list(metaDef) =>
  switch (items) {
  | [] => []
  | [{value: Identifier("schema"), _}, next, ...rest] =>
    [SchemaDef(parseBinding(next)), ...scanMetaDefs(rest)]
  | [item, ...rest] =>
    [mlToMetaDef(item), ...scanMetaDefs(rest)]
  }

and buildBlock = (keyword, contents, rest): ml => {
  let body = buildItems(contents);
  switch (keyword) {
  | "postulate" =>
    let decls = List.map(mlToDecl, body);
    let blockML = mk(Ap(mk(Identifier("__postulate")), List.map(declToML, decls)));
    switch (rest) {
    | Some(r) => mk(Ap(mk(Identifier("__seq")), [blockML, r]))
    | None => blockML
    };
  | "meta" =>
    let defs = scanMetaDefs(body);
    let blockML = mk(Ap(mk(Identifier("__meta")), List.map(metaDefToML, defs)));
    switch (rest) {
    | Some(r) => mk(Ap(mk(Identifier("__seq")), [blockML, r]))
    | None => blockML
    };
  | "construct" =>
    switch (body, rest) {
    | ([], Some(r)) => r
    | ([by, ...decls], _) =>
      let schemaName = extractName(by);
      let declList = List.map(mlToDecl, decls);
      let blockML = mk(Ap(mk(Identifier("__construct")), [mk(Identifier(schemaName)), ...List.map(declToML, declList)]));
      switch (rest) {
      | Some(r) => mk(Ap(mk(Identifier("__seq")), [blockML, r]))
      | None => blockML
      };
    | ([], None) =>
      let blockML = mk(Ap(mk(Identifier("__construct")), [mk(Hole(Synthesized))]));
      blockML
    }
  | "by" =>
    switch (body) {
    | [name, ...decls] =>
      let schemaName = extractName(name);
      let declList = List.map(mlToDecl, decls);
      mk(Ap(mk(Identifier("__construct")), [mk(Identifier(schemaName)), ...List.map(declToML, declList)]))
    | [] =>
      mk(Ap(mk(Identifier("__construct")), [mk(Hole(Synthesized))]))
    }
  | _ => mk(BuilderError)
  };
}

and extractName = (t: ml): string =>
  switch (t.value) {
  | Identifier(name) => name
  | _ => "_"
  }

/* Convert an ml expression (from the intermediate representation) into a decl.
   A declaration looks like:
   - `name : retType` => Ap(Identifier(":"), [Identifier(name), retType])
   - `(name (p1 : T1) ...) : retType` => Ap(Identifier(":"), [Ap(Identifier(name), [...]), retType])
   The inner Ap for params contains items like Ap(Identifier(":"), [Identifier(pname), ptype])
*/
and mlToDecl = (t: ml): decl => {
  switch (t.value) {
  /* (name params...) : retType */
  | Ap({value: Identifier(":"), _}, [lhs, retTypeExpr]) =>
    switch (lhs.value) {
    /* name : retType — no params */
    | Identifier(name) =>
      {declName: name, params: [], retType: mlToOL(retTypeExpr), declMeta: t.meta}
    /* (name p1 p2 ...) : retType — with params */
    | Ap({value: Identifier(name), _}, paramExprs) =>
      let params = List.map(mlToParam, paramExprs);
      {declName: name, params, retType: mlToOL(retTypeExpr), declMeta: t.meta}
    | _ =>
      {declName: "_", params: [], retType: mlToOL(retTypeExpr), declMeta: t.meta}
    }
  /* No colon — just a name or application, treat as decl with hole retType */
  | Identifier(name) =>
    {declName: name, params: [], retType: mkOL(OLHole(Synthesized)), declMeta: t.meta}
  | _ =>
    {declName: "_", params: [], retType: mkOL(OLHole(Synthesized)), declMeta: t.meta}
  };
}

and mlToParam = (t: ml): param => {
  switch (t.value) {
  /* (pname : ptype) — annotated param */
  | Ap({value: Identifier(":"), _}, [{value: Identifier(name), _}, typeExpr]) =>
    {paramName: name, paramType: mlToOL(typeExpr), paramMeta: t.meta}
  /* bare identifier — untyped param, use hole for type */
  | Identifier(name) =>
    {paramName: name, paramType: mkOL(OLHole(Synthesized)), paramMeta: t.meta}
  | _ =>
    {paramName: "_", paramType: mkOL(OLHole(Synthesized)), paramMeta: t.meta}
  };
}

/* Convert ml intermediate expression to an OL term */
and mlToOL = (t: ml): ol => {
  let value =
    switch (t.value) {
    | Hole(k) => OLHole(k)
    | Identifier(s) => OLIdentifier(s)
    | Ap(f, args) => OLAp(mlToOL(f), List.map(mlToOL, args))
    | _ => OLHole(Synthesized)
    };
  {value, meta: t.meta};
}

/* Convert ml expression to a metaDef.
   In meta blocks, items are either:
   - `schema name : type = body` — SchemaDef
   - `name : type = body` or `name = body` — LetDef
*/
and mlToMetaDef = (t: ml): metaDef => {
  switch (t.value) {
  /* schema name ... — the Ap has schema as head */
  | Ap({value: Identifier("schema"), _}, [rest]) =>
    SchemaDef(parseBinding(rest))
  | Ap({value: Identifier("schema"), _}, items) =>
    /* schema followed by a binding expression: recombine the items */
    let combined = combineTerms(items);
    SchemaDef(parseBinding(combined))
  | _ =>
    LetDef(parseBinding(t))
  };
}

/* Convert a decl back to ml for block representation */
and declToML = (d: decl): ml => {
  let nameTerm = mk(Identifier(d.declName));
  let retTerm = olToML(d.retType);
  let lhs =
    switch (d.params) {
    | [] => nameTerm
    | params =>
      let paramTerms = List.map(p => {
        let n = mk(Identifier(p.paramName));
        let ty = olToML(p.paramType);
        let asc = mk(Ap(mk(Identifier(":")), [n, ty]));
        {...asc, meta: {...asc.meta, parens: true}};
      }, params);
      let ap = mk(Ap(nameTerm, paramTerms));
      {...ap, meta: {...ap.meta, parens: true}};
    };
  mk(Ap(mk(Identifier(":")), [lhs, retTerm]));
}

and mlTypeToExpr = (ty: mlType): ml =>
  switch (ty) {
  | MTerm => mk(Identifier("Term"))
  | MSort => mk(Identifier("Sort"))
  | MBool => mk(Identifier("Bool"))
  | MString => mk(Identifier("String"))
  | MList(t) => mk(Ap(mk(Identifier("List")), [mlTypeToExpr(t)]))
  | MResult(t) => mk(Ap(mk(Identifier("Result")), [mlTypeToExpr(t)]))
  | MTuple(items) => mk(Tuple(List.map(mlTypeToExpr, items)))
  | MArrow(a, b) => mk(Ap(mk(Identifier("->")), [mlTypeToExpr(a), mlTypeToExpr(b)]))
  }

and metaDefToML = (d: metaDef): ml => {
  let bindingToML = (b: binding): ml => {
    let nameTerm = mk(Identifier(b.name));
    let lhs =
      switch (b.annotation, b.rawAnnotation) {
      | (Some(ty), _) =>
        mk(Ap(mk(Identifier(":")), [nameTerm, mlTypeToExpr(ty)]))
      | (None, Some(rawExpr)) =>
        /* Annotation couldn't parse — preserve raw expression for error reporting */
        mk(Ap(mk(Identifier(":")), [nameTerm, rawExpr]))
      | (None, None) => nameTerm
      };
    mk(Ap(mk(Identifier("=")), [lhs, b.rhs]));
  };
  switch (d) {
  | LetDef(b) => bindingToML(b)
  | SchemaDef(b) =>
    mk(Ap(mk(Identifier("schema")), [bindingToML(b)]))
  };
}

and olToML = (t: ol): ml => {
  let value =
    switch (t.value) {
    | OLHole(k) => Hole(k)
    | OLIdentifier(s) => Identifier(s)
    | OLAp(f, args) => Ap(olToML(f), List.map(olToML, args))
    };
  {value, meta: t.meta};
}

and buildBlocks = (form, contents, rest): ml => {
  let keyword = faceToken(form);
  switch (form) {
  | CHead(_) => buildBlock(keyword, contents, rest)
  | CMatch(inner, innerItems, _) =>
    buildBlocks(inner, innerItems, Some(buildBlock(keyword, contents, rest)))
  };
}

/* --- Infix builder helper --- */

and buildInfix = (constructor, left, leftUf, tok, rightUf, right) =>
  localize(mk(constructor(buildLeftChild(left, leftUf), buildChild(rightUf, right))), tok)

/* === Main form builder === */

and buildForm = (form: openForm): ml => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* Bracket forms: (...), [...], with commas */
  | (None, [], CMatch(_, _, {value: TNamed(")" | "]"), _}), [], None) =>
    let (open_, elementGroups) = collectBracketElements(closed);
    let elements = List.map(buildTerms, elementGroups);
    switch (open_, elements) {
    | ("(", [single]) => {...single, meta: {...single.meta, parens: true}}
    | ("(", elements) =>
      let t = mk(Tuple(elements));
      {...t, meta: {...t.meta, parens: true}}
    | ("[", items) =>
      switch (List.rev(items)) {
      | [{value: Hole(Synthesized), _}] =>
        /* [] with nothing inside — empty list */
        mk(List([]))
      | _ => mk(List(items))
      }
    | _ => mk(BuilderError)
    };

  /* Atoms */
  | (None, [], CHead({value: TAtom(Hole), _} as tok), [], None) =>
    localize(mk(Hole(User)), tok)
  | (None, [], CHead({value: TAtom(Identifier(v)), _} as tok), [], None) =>
    localize(mk(Identifier(v)), tok)
  | (None, [], CHead({value: TAtom(StringLit(s)), _} as tok), [], None) =>
    localize(mk(StringLit(s)), tok)

  /* fun(pats)=>f — body captured by =>f_face's right-precedence */
  | (_, _, CMatch(CHead({value: TNamed("fun"), _}), patItems, {value: TNamed("=>" | "=>f"), _}), _, _) =>
    let pats = buildFunPats(patItems);
    let body = buildChild(rightUf, right);
    mk(Fun(pats, body))

  /* let(name)=let(rhs) in(body) — bare let binding */
  | (_, _, CMatch(
      CMatch(CHead({value: TNamed("let"), _}), nameItems, {value: TNamed("=let"), _}),
      rhsItems,
      {value: TNamed("in"), _}
    ), _, _) =>
    let name = nameFromItems(nameItems);
    let rhs = buildTerms(rhsItems);
    let body = buildChild(rightUf, right);
    mk(Let({name, annotation: None, rawAnnotation: None, rhs, bindingMeta: defaultMeta}, body))

  /* let(name):let(type)=let(rhs) in(body) — annotated let binding */
  | (_, _, CMatch(
      CMatch(
        CMatch(CHead({value: TNamed("let"), _}), nameItems, {value: TNamed(":let"), _}),
        typeItems,
        {value: TNamed("=let"), _}
      ),
      rhsItems,
      {value: TNamed("in"), _}
    ), _, _) =>
    let name = nameFromItems(nameItems);
    let typeExpr = buildTerms(typeItems);
    let annotation = mlToType(typeExpr);
    let rhs = buildTerms(rhsItems);
    let body = buildChild(rightUf, right);
    mk(Let({name, annotation, rawAnnotation: Some(typeExpr), rhs, bindingMeta: defaultMeta}, body))

  /* Infix :: → Cons */
  | (_, _, CHead({value: TNamed("::"), _} as tok), _, _) =>
    buildInfix((l, r) => Cons(l, r), left, leftUf, tok, rightUf, right)

  /* Infix : → intermediate Ap(Identifier(":"), [l, r]) */
  | (_, _, CHead({value: TNamed(":"), _} as tok), _, _) =>
    buildInfix((l, r) => Ap(mk(Identifier(":")), [l, r]), left, leftUf, tok, rightUf, right)

  /* Infix -> → intermediate Ap(Identifier("->"), [l, r]) */
  | (_, _, CHead({value: TNamed("->"), _} as tok), _, _) =>
    buildInfix((l, r) => Ap(mk(Identifier("->")), [l, r]), left, leftUf, tok, rightUf, right)

  /* Infix = → intermediate Ap(Identifier("="), [l, r]) */
  | (_, _, CHead({value: TNamed("="), _} as tok), _, _) =>
    buildInfix((l, r) => Ap(mk(Identifier("=")), [l, r]), left, leftUf, tok, rightUf, right)

  /* Infix == → BinOp(Eq, ...) */
  | (_, _, CHead({value: TNamed("=="), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(Eq, l, r), left, leftUf, tok, rightUf, right)

  /* Infix != → BinOp(Neq, ...) */
  | (_, _, CHead({value: TNamed("!="), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(Neq, l, r), left, leftUf, tok, rightUf, right)

  /* Infix && → BinOp(And, ...) */
  | (_, _, CHead({value: TNamed("&&"), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(And, l, r), left, leftUf, tok, rightUf, right)

  /* Infix || → BinOp(Or, ...) */
  | (_, _, CHead({value: TNamed("||"), _} as tok), _, _) =>
    buildInfix((l, r) => BinOp(Or, l, r), left, leftUf, tok, rightUf, right)

  /* match...with...|...=>...end */
  | (_, _, CMatch(_, _, {value: TNamed("end"), _}), _, _) when isMatchChain(closed) =>
    buildMatchChain(closed)

  /* if...then...else...end */
  | (_, _, CMatch(_, _, {value: TNamed("end"), _}), _, _) when isIfChain(closed) =>
    buildIfChain(closed)

  /* Keyword atoms — these produce identifiers */
  | (None, [], CHead({value: TNamed(name), _} as tok), [], None) =>
    localize(mk(Identifier(name)), tok)

  /* Other blocks terminated by `end` */
  | (_, _, CMatch(inner, innerItems, {value: TNamed("end"), _}), [], None) =>
    buildBlocks(inner, innerItems, None)

  /* Catch-all infix — produce Ap(Identifier(op), [l, r]) as intermediate */
  | (_, _, CHead({value: TNamed(op), _} as tok), _, _) =>
    buildInfix((l, r) => Ap(mk(Identifier(op)), [l, r]), left, leftUf, tok, rightUf, right)

  | _ => mk(BuilderError)
  };
}

and buildUnform =
  fun
  | USecondary(_) => []
  | UShard(token) => [localize(mk(Shard(token.value)), token)]

and buildUnforms = unforms => List.concat_map(buildUnform, unforms)

and buildSharded =
  fun
  | Unform(u) => buildUnform(u)
  | Form(f) => [buildForm(f)];

let build = (forms: list(sharded(openForm))): ml => buildTerms(forms);
