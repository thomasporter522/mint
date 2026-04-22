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
  | [first, ...rest] => {
      let last = List.fold_left((_, x) => x, first, rest);
      let t = mk(Ap(first, rest));
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

let isAscSeparator = (tok: primaryToken): bool =>
  switch (tok) {
  | TNamed(":p") => true
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
  | CMatch(inner, items, {value, _}) when isCommaToken(value) || value == TNamed(")") || value == TNamed("]") =>
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
  /* Parens: (...) — just recurse, preserving parens flag.
     Meta range spans from the opening ( to the closing ) so error
     localization on a paren-wrapped term covers the full source. */
  | (None, CMatch(_, _, {value: TNamed(")"), _} as closeTok), None) =>
    let (_, elementGroups) = collectBracketElements(closed);
    switch (elementGroups) {
    | [single] =>
      let inner = buildOLTerms(single);
      let openTok = Parser.headOf(closed);
      {...inner, meta: {parens: true, start: openTok.start, end_: closeTok.end_}}
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
  | CMatch(_, _, {value: TNamed(")"), _} as closeTok) =>
    let (_, elementGroups) = collectBracketElements(cf);
    switch (elementGroups) {
    | [single] =>
      let inner = buildOLTerms(single);
      let openTok = Parser.headOf(cf);
      {...inner, meta: {parens: true, start: openTok.start, end_: closeTok.end_}}
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
      let last = List.fold_left((_, x) => x, first, rest);
      {value: OLAp(first, rest), meta: metaFromRange(first.meta.start, last.meta.end_)};
    }

/* Build OL terms from sharded items — like buildTerms but for OL */
and buildOLTerms = (items: list(sharded(openForm))): ol =>
  combineOLTerms(List.concat_map(buildOLSharded, items))

/* Extract a bare identifier name from a solitary form. */
and extractBareName = (f: openForm): option(string) =>
  if (f.left != None || f.right != None) {
    None;
  } else {
    switch (f.closed) {
    | CHead({value: TAtom(Identifier(n)), _}) => Some(n)
    | CHead({value: TNamed(n), _}) => Some(n)
    | _ => None
    };
  }

/* Build a param from a solitary form.
   Typed:   (name :p type)  →  CMatch(CMatch(CHead("("), nameItems, ":p"), typeItems, ")")
   Untyped: bare identifier */
and buildParamForm = (f: openForm): param =>
  switch (f.closed) {
  | CMatch(
      CMatch(CHead({value: TNamed("("), _}), nameItems, {value: TNamed(":p"), _}),
      typeItems,
      {value: TNamed(")"), _},
    ) when f.left == None && f.right == None =>
    let name = nameFromItems(nameItems);
    let paramType = buildOLTerms(typeItems);
    {paramName: name, paramType, paramMeta: defaultMeta}
  | _ =>
    switch (extractBareName(f)) {
    | Some(name) =>
      {paramName: name, paramType: mkOL(OLHole(Synthesized)), paramMeta: defaultMeta}
    | None =>
      {paramName: "_", paramType: mkOL(OLHole(Synthesized)), paramMeta: defaultMeta}
    }
  }

/* Parse a (name param1 param2 ...) spine paren group from the closedForm.
   Returns (name, params) if the structure matches, else None. */
and buildSpineParams = (spineClosed: closedForm): option((string, list(param))) =>
  switch (spineClosed) {
  | CMatch(CHead({value: TNamed("("), _}), items, {value: TNamed(")"), _}) =>
    let forms =
      List.filter_map(fun | Form(f) => Some(f) | Unform(_) => None, items);
    switch (forms) {
    | [nameForm, ...paramForms] =>
      switch (extractBareName(nameForm)) {
      | Some(name) => Some((name, List.map(buildParamForm, paramForms)))
      | None => None
      }
    | [] => None
    }
  | _ => None
  }

/* Build a decl directly from an openForm.
   Declarations are either:
   - name : retType               (: as infix, lhs is a bare name)
   - (name params...) : retType   (: as infix, lhs is a paren spine group)
   - bare name                    (no colon, for construct blocks) */
and buildDeclFromForm = (form: openForm): decl => {
  switch (form.closed) {
  /* Infix : — declaration with type annotation */
  | CHead({value: TNamed(":"), _}) =>
    let retType = buildOLChild(form.rightUf, form.right);
    switch (form.left) {
    | Some(lhsForm) =>
      switch (buildSpineParams(lhsForm.closed)) {
      | Some((name, params)) =>
        {declName: name, params, retType, declMeta: formMeta(form)}
      | None =>
        switch (extractBareName(lhsForm)) {
        | Some(name) =>
          {declName: name, params: [], retType, declMeta: formMeta(form)}
        | None =>
          {declName: "_", params: [], retType, declMeta: formMeta(form)}
        }
      }
    | None =>
      {declName: "_", params: [], retType, declMeta: formMeta(form)}
    };

  /* Bare identifier — no colon */
  | _ =>
    switch (extractBareName(form)) {
    | Some(name) =>
      {declName: name, params: [], retType: mkOL(OLHole(Synthesized)), declMeta: formMeta(form)}
    | None =>
      {declName: "_", params: [], retType: mkOL(OLHole(Synthesized)), declMeta: formMeta(form)}
    }
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

/* Lossy: convert an ml expression back to an OL term. Any non-OL
   construct becomes a synthesized hole. */
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

/* Extract a param from an ML expression (used when lhs of : is a paren group
   that was built via buildLeftChild, which goes through buildForm).
   A (name : type) param is represented as Asc(Identifier(name), typeExpr). */
and extractParamFromML = (t: ml): param =>
  switch (t.value) {
  | Asc({value: Identifier(name), _}, typeExpr) =>
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

and isSchemaForm = (form: openForm): bool =>
  switch (form.closed) {
  | CHead({value: TNamed("schema"), _}) => true
  | _ => false
  }

and scanMetaSharded = (items: list(sharded(openForm))): list(metaDef) =>
  switch (items) {
  | [] => []
  /* Skip leading unforms */
  | [Unform(_), ...rest] => scanMetaSharded(rest)
  /* schema keyword followed by a form (possibly with unforms between) */
  | [Form(f), ...rest] when isSchemaForm(f) =>
    let rec dropUnforms = fun
      | [Unform(_), ...xs] => dropUnforms(xs)
      | xs => xs;
    switch (dropUnforms(rest)) {
    | [Form(defForm), ...tail] =>
      [SchemaDef(buildBindingFromForm(defForm)), ...scanMetaSharded(tail)]
    | _ =>
      /* schema with no following form: record as invalid SchemaDef with empty binding */
      scanMetaSharded(rest)
    };
  /* Regular form → LetDef */
  | [Form(f), ...rest] =>
    [buildMetaDefFromForm(f), ...scanMetaSharded(rest)]
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
    | Asc({value: Identifier(name), _}, typeExpr) =>
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
   Returns None if the keyword is not a program block keyword — that lets
   buildProgram cleanly reject match/if chains that also use `end`. */
and buildBlockFromForm = (keyword: string, contents: list(sharded(openForm))): option(block) =>
  switch (keyword) {
  | "postulate" =>
    let decls = List.filter_map(buildDeclFromSharded, contents);
    Some(Postulate(decls))
  | "meta" =>
    let defs = buildMetaDefItems(contents);
    Some(Meta(defs))
  | "construct" =>
    /* construct with no `by` — empty schema name */
    Some(Construct("_", List.filter_map(buildDeclFromSharded, contents)))
  | "by" =>
    /* `by` contents: schema name token followed by declarations.
       Skip leading unforms (whitespace) before the name. */
    let rec skipUnforms = fun
      | [Unform(_), ...xs] => skipUnforms(xs)
      | xs => xs;
    let nameAndRest = skipUnforms(contents);
    let (name, declItems) =
      switch (nameAndRest) {
      | [Form(f), ...rest] =>
        switch (f.closed) {
        | CHead({value: TAtom(Identifier(n)), _})
        | CHead({value: TNamed(n), _}) when f.left == None && f.right == None =>
          (n, rest)
        | _ => ("_", nameAndRest)
        }
      | _ => ("_", nameAndRest)
      };
    Some(Construct(name, List.filter_map(buildDeclFromSharded, declItems)))
  | _ => None
  }

/* Walk the CMatch structure to collect blocks for a program.
   Returns None if any link in the chain is not a program keyword.
   The "construct" keyword is a syntactic opener that pairs with "by" —
   "by" carries the schema name and decls, so we skip the "construct" level. */
and collectBlocks = (form: closedForm, contents: list(sharded(openForm))): option(list(block)) =>
  switch (form) {
  /* `construct` is a syntactic opener — the enclosing `by` produces the block.
     Skip it both when it appears as a bare head (lone `construct by X ... end`
     chain) and when it appears as the closer of a sub-chain (postulate...
     meta...construct...by chains). */
  | CHead({value: TNamed("construct"), _}) => Some([])
  | CMatch(inner, innerItems, {value: TNamed("construct"), _}) =>
    collectBlocks(inner, innerItems)
  | CHead({value: TNamed(keyword), _}) =>
    switch (buildBlockFromForm(keyword, contents)) {
    | Some(b) => Some([b])
    | None => None
    }
  | CMatch(inner, innerItems, {value: TNamed(keyword), _}) =>
    switch (collectBlocks(inner, innerItems), buildBlockFromForm(keyword, contents)) {
    | (Some(prev), Some(b)) => Some(prev @ [b])
    | _ => None
    }
  | _ => None
  }

/* Top-level entry point: walk the forms and produce a program (list of blocks).
   Returns [] when the input is not program-shaped (e.g. a bare expression). */
and buildProgram = (forms: list(sharded(openForm))): program => {
  let blocks = List.concat_map(
    fun
    | Form(form) =>
      switch (form.closed) {
      | CMatch(inner, innerItems, {value: TNamed("end"), _}) =>
        switch (collectBlocks(inner, innerItems)) {
        | Some(bs) => bs
        | None => []
        }
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

/* --- Infix builder helper --- */

and buildInfix = (constructor, left, leftUf, tok, rightUf, right) =>
  localize(mk(constructor(buildLeftChild(left, leftUf), buildChild(rightUf, right))), tok)

/* === Main form builder === */

and buildForm = (form: openForm): ml => {
  let {left, leftUf, closed, rightUf, right} = form;

  switch (left, leftUf, closed, rightUf, right) {
  /* (name :p type) — ascription inside parens */
  | (None, [], CMatch(CMatch(CHead({value: TNamed("("), _}), lhsItems, {value: TNamed(":p"), _}), rhsItems, {value: TNamed(")"), _}), [], None) =>
    let l = buildTerms(lhsItems);
    let r = buildTerms(rhsItems);
    let t = mk(Asc(l, r));
    {...t, meta: {...t.meta, parens: true}}

  /* Bracket forms: (...), [...], with commas.
     Meta range spans the full bracket pair so localization on a bracket-
     wrapped term covers the entire source including the delimiters. */
  | (None, [], CMatch(_, _, {value: TNamed(")" | "]"), _} as closeTok), [], None) =>
    let (open_, elementGroups) = collectBracketElements(closed);
    let elements = List.map(buildTerms, elementGroups);
    let openTok = Parser.headOf(closed);
    let withSpan = (t: ml) =>
      {...t, meta: {parens: true, start: openTok.start, end_: closeTok.end_}};
    switch (open_, elements) {
    | ("(", [single]) => withSpan(single)
    | ("(", elements) => withSpan(mk(Tuple(elements)))
    | ("[", items) =>
      let list =
        switch (List.rev(items)) {
        | [{value: Hole(Synthesized), _}] =>
          /* [] with nothing inside — empty list */
          mk(List([]))
        | _ => mk(List(items))
        };
      {...list, meta: {...list.meta, start: openTok.start, end_: closeTok.end_}}
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

  /* Infix : → Asc(l, r) */
  | (_, _, CHead({value: TNamed(":"), _} as tok), _, _) =>
    buildInfix((l, r) => Asc(l, r), left, leftUf, tok, rightUf, right)

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
