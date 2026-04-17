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
