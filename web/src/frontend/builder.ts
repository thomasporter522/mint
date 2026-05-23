/* Walk a Lezer tree, produce an AST mirroring reason/src/Term.re.
   The Lezer tree is positional only (every node has a type and a span);
   actual text is read from the source string. */

import type { SyntaxNode, Tree } from '@lezer/common'
import type {
  Meta, OL, ML, Pat, DeclLine, DeclArg, LetBinding, Binding, MetaDef, Block,
  Program, MLType, OLLine, StringMeta, TagLine,
} from './ast.ts'
import { mkOL, mkML, mkPat, embedOL } from './ast.ts'

/* === Helpers === */

function metaOf(node: SyntaxNode, parens = false): Meta {
  return { parens, start: node.from, end: node.to }
}

function text(node: SyntaxNode, src: string): string {
  return src.slice(node.from, node.to)
}

function children(node: SyntaxNode): SyntaxNode[] {
  const out: SyntaxNode[] = []
  for (let c = node.firstChild; c; c = c.nextSibling) out.push(c)
  return out
}

function childrenByName(node: SyntaxNode, name: string): SyntaxNode[] {
  return children(node).filter(c => c.name === name)
}

function firstChildByName(node: SyntaxNode, name: string): SyntaxNode | null {
  for (let c = node.firstChild; c; c = c.nextSibling) if (c.name === name) return c
  return null
}

/* === OL building ===
   An OL term comes from a TypeExpr / TypeApp / TypeAtom / ParenInner /
   AtomExpr context. OL now has just two shapes — holes and applications
   keyed by a bare identifier head; everything else degrades to a hole. */

/* Extract the head identifier of an application as a StringMeta.
   Built OL terms produced by `buildOL` are always zero-arg `OLAp` for
   bare identifiers, so the head reuses that node's `f`. */
function olToHead(t: OL, fallbackMeta: Meta): StringMeta {
  if (t.value.kind === 'OLAp' && t.value.args.length === 0) {
    return t.value.f
  }
  return { string: '_', meta: fallbackMeta }
}

export function buildOL(node: SyntaxNode, src: string): OL {
  const m = metaOf(node)
  switch (node.name) {
    case 'TypeExpr':
    case 'TypeBinary': {
      const c = node.firstChild
      if (!c) return mkOL({ kind: 'OLHole' }, m)
      // Single-child wrapper
      if (!c.nextSibling) return buildOL(c, src)
      // For arrow types, etc., we currently degrade to a synthesized hole.
      // The semantics of arrow types in OL position is rare; revisit when
      // examples need it.
      return mkOL({ kind: 'OLHole' }, m)
    }
    case 'TypeApp': {
      const cs = children(node)
      if (cs.length === 0) return mkOL({ kind: 'OLHole' }, m)
      const headOL = buildOL(cs[0], src)
      const f = olToHead(headOL, metaOf(cs[0]))
      const args = cs.slice(1).map(c => buildOL(c, src))
      return mkOL({ kind: 'OLAp', f, args }, m)
    }
    case 'TypeAtom':
    case 'AtomExpr':
    case 'ParenInner': {
      const c = node.firstChild
      if (!c) return mkOL({ kind: 'OLHole' }, m)
      if (c.name === 'LParen' || c.name === 'LBracket') {
        // Parenthesized — recurse into the inner expr (skip LParen/RParen).
        const inner = c.nextSibling
        if (!inner || inner.name === 'RParen' || inner.name === 'RBracket') {
          return mkOL({ kind: 'OLHole' }, m)
        }
        const result = buildOL(inner, src)
        // Record parens; extend start/end to cover them.
        return {
          ...result,
          meta: { ...result.meta, parens: true, start: m.start, end: m.end },
        }
      }
      return buildOL(c, src)
    }
    case 'Identifier': {
      // Bare identifiers become zero-arg OLAp so every applied form goes
      // through one shape. The StringMeta carries the identifier's own
      // range; the outer OLAp's meta initially matches it.
      const f: StringMeta = { string: text(node, src), meta: m }
      return mkOL({ kind: 'OLAp', f, args: [] }, m)
    }
    case 'Hole':
    case 'Auto':
    case 'Wildcard':
      return mkOL({ kind: 'OLHole' }, m)
    case 'AppInner': {
      const cs = children(node)
      if (cs.length === 0) return mkOL({ kind: 'OLHole' }, m)
      const headOL = buildOL(cs[0], src)
      const f = olToHead(headOL, metaOf(cs[0]))
      const args = cs.slice(1).map(c => buildOL(c, src))
      return mkOL({ kind: 'OLAp', f, args }, m)
    }
    case 'CommaSep': {
      // Single element passes through; multiple = tuple, not representable in OL.
      const first = node.firstChild
      if (!first) return mkOL({ kind: 'OLHole' }, m)
      return buildOL(first, src)
    }
    default:
      return mkOL({ kind: 'OLHole' }, m)
  }
}

/* === Decl building === */

function buildDeclArgs(node: SyntaxNode, src: string): DeclArg[] {
  // Param { LParen Identifier+ ":" TypeExpr RParen }
  // A grouped form like `(l1 l2 : level)` expands into multiple DeclArg
  // records, each sharing the same declArgType.
  const ids = childrenByName(node, 'Identifier')
  const ty = firstChildByName(node, 'TypeExpr')
  const declArgType = ty ? buildOL(ty, src) : mkOL({ kind: 'OLHole' })
  const groupMeta = metaOf(node)
  if (ids.length === 0) {
    return [{
      declArgName: { string: '_', meta: groupMeta },
      declArgType,
      declArgMeta: groupMeta,
    }]
  }
  return ids.map(id => ({
    declArgName: { string: text(id, src), meta: metaOf(id) },
    declArgType,
    declArgMeta: groupMeta,
  }))
}

function buildDeclLine(node: SyntaxNode, src: string): DeclLine {
  // Decl { ItemHead (":" TypeExpr)? }
  // ItemHead { Identifier Param* | LParen Identifier Param* RParen }
  const head = firstChildByName(node, 'ItemHead')
  const ty = firstChildByName(node, 'TypeExpr')
  let declName: StringMeta = { string: '_', meta: metaOf(node) }
  let args: DeclArg[] = []
  if (head) {
    const hid = firstChildByName(head, 'Identifier')
    if (hid) {
      declName = { string: text(hid, src), meta: metaOf(hid) }
    }
    args = childrenByName(head, 'Param').flatMap(p => buildDeclArgs(p, src))
  }
  const retType = ty
    ? buildOL(ty, src)
    : mkOL({ kind: 'OLHole' })
  return { declName, args, retType, declMeta: metaOf(node) }
}

/* === Pattern building === */

export function buildPat(node: SyntaxNode, src: string): Pat {
  const m = metaOf(node)
  switch (node.name) {
    case 'Pattern': {
      const c = node.firstChild
      if (!c) return mkPat({ kind: 'PWildcard' }, m)
      return buildPat(c, src)
    }
    case 'PatBinary': {
      // Pattern :: Pattern (cons). Children: [Pattern, "::", Pattern].
      const cs = children(node).filter(c => c.name === 'Pattern')
      if (cs.length >= 2) {
        return mkPat({ kind: 'PCons', head: buildPat(cs[0], src), tail: buildPat(cs[1], src) }, m)
      }
      return mkPat({ kind: 'PWildcard' }, m)
    }
    case 'PatApp': {
      // Head must be a bare identifier (the OL constructor name);
      // everything else degrades to a wildcard.
      const cs = children(node)
      if (cs.length === 0) return mkPat({ kind: 'PWildcard' }, m)
      const headNode = cs[0]
      const headName = headNode.name === 'Identifier' ? text(headNode, src) : '_'
      const args = cs.slice(1).map(c => buildPat(c, src))
      return mkPat({ kind: 'POLAp', head: headName, args }, m)
    }
    case 'PatAtom': {
      const c = node.firstChild
      if (!c) return mkPat({ kind: 'PWildcard' }, m)
      if (c.name === 'LParen') return buildPatParens(node, src, m)
      if (c.name === 'LBracket') return buildPatList(node, src, m)
      return buildPat(c, src)
    }
    case 'Identifier':
      return mkPat({ kind: 'PVar', name: text(node, src) }, m)
    case 'Wildcard':
    case 'Hole':
      return mkPat({ kind: 'PWildcard' }, m)
    case 'StringLit': {
      const raw = text(node, src)
      return mkPat({ kind: 'PString', value: raw.slice(1, -1) }, m)
    }
    default:
      return mkPat({ kind: 'PWildcard' }, m)
  }
}

function buildPatParens(node: SyntaxNode, src: string, m: Meta): Pat {
  // PatAtom { LParen CommaSep<Pattern>? RParen }
  const cs = childrenByName(node, 'CommaSep')
  const items: Pat[] = []
  if (cs.length > 0) {
    for (const c of children(cs[0])) {
      if (c.name === 'Pattern') items.push(buildPat(c, src))
    }
  }
  if (items.length === 1) {
    return { ...items[0], meta: { ...items[0].meta, parens: true, start: m.start, end: m.end } }
  }
  return mkPat({ kind: 'PTuple', items }, { ...m, parens: true })
}

function buildPatList(node: SyntaxNode, src: string, m: Meta): Pat {
  const cs = childrenByName(node, 'CommaSep')
  const items: Pat[] = []
  if (cs.length > 0) {
    for (const c of children(cs[0])) {
      if (c.name === 'Pattern') items.push(buildPat(c, src))
    }
  }
  return mkPat({ kind: 'PList', items }, m)
}

/* === ML expression building === */

export function buildML(node: SyntaxNode, src: string): ML {
  const m = metaOf(node)
  switch (node.name) {
    case 'Expr':
    case 'ExprNoEq': {
      const c = node.firstChild
      if (!c) return mkML({ kind: 'Hole' }, m)
      return buildML(c, src)
    }
    case 'BinaryExpr':
    case 'BinaryInner':
    case 'TopBinaryExpr':
      return buildBinary(node, src)
    case 'TopExpr': {
      const c = node.firstChild
      if (!c) return mkML({ kind: 'Hole' }, m)
      return buildML(c, src)
    }
    case 'AppInner': {
      const cs = children(node)
      if (cs.length === 0) return mkML({ kind: 'Hole' }, m)
      const head = buildML(cs[0], src)
      const args = cs.slice(1).map(c => buildML(c, src))
      return mkML({ kind: 'Ap', f: head, args }, m)
    }
    case 'AtomExpr':
    case 'ParenInner': {
      const c = node.firstChild
      if (!c) return mkML({ kind: 'Hole' }, m)
      if (c.name === 'LParen') return buildParenExpr(node, src, m)
      if (c.name === 'LBracket') return buildListExpr(node, src, m)
      return buildML(c, src)
    }
    case 'Identifier':
      return mkML({ kind: 'Identifier', name: text(node, src) }, m)
    case 'Hole':
    case 'Wildcard':
      return mkML({ kind: 'Hole' }, m)
    case 'StringLit': {
      const raw = text(node, src)
      return mkML({ kind: 'StringLit', value: raw.slice(1, -1) }, m)
    }
    case 'Tag': {
      const lex = text(node, src)
      return mkML({ kind: 'TagLit', name: lex.startsWith('#') ? lex.slice(1) : lex }, m)
    }
    case 'Fun':
      return buildFun(node, src, m)
    case 'Match':
      return buildMatch(node, src, m)
    case 'If':
      return buildIf(node, src, m)
    case 'Let':
      return buildLet(node, src, m)
    case 'TypeExpr':
    case 'TypeApp':
    case 'TypeAtom':
    case 'TypeBinary':
      // Type expressions appearing in ML context (e.g. let annotations) —
      // recurse with the same logic; the structure is identical to ML
      // sans control flow.
      return embedOL(buildOL(node, src))
    default:
      return mkML({ kind: 'Hole' }, m)
  }
}

function buildBinary(node: SyntaxNode, src: string): ML {
  const cs = children(node)
  // Find the operator child (a literal token). Children layout:
  //   Expr <op> Expr
  if (cs.length < 3) return mkML({ kind: 'Hole' }, metaOf(node))
  const left = buildML(cs[0], src)
  const opNode = cs[1]
  const right = buildML(cs[2], src)
  const opText = text(opNode, src)
  const m = metaOf(node)
  switch (opText) {
    case '->':
      return mkML({
        kind: 'Ap',
        f: mkML({ kind: 'Identifier', name: '->' }),
        args: [left, right],
      }, m)
    case '=':
      return mkML({
        kind: 'Ap',
        f: mkML({ kind: 'Identifier', name: '=' }),
        args: [left, right],
      }, m)
    case ':':
      // Ascription is no longer a first-class ML form; the type
      // annotation gets dropped here. Annotations on let/meta-def
      // bindings are still captured separately via the binding's
      // `rawAnnotation`.
      return { ...left, meta: { ...left.meta, start: m.start, end: m.end } }
    case '::':
      return mkML({ kind: 'Cons', head: left, tail: right }, m)
    case '==':
      return mkML({ kind: 'BinOp', op: 'Eq', left, right }, m)
    case '!=':
      return mkML({ kind: 'BinOp', op: 'Neq', left, right }, m)
    case '&&':
      return mkML({ kind: 'BinOp', op: 'And', left, right }, m)
    case '||':
      return mkML({ kind: 'BinOp', op: 'Or', left, right }, m)
    default:
      return mkML({ kind: 'Hole' }, m)
  }
}

function buildParenExpr(node: SyntaxNode, src: string, m: Meta): ML {
  const commaSep = firstChildByName(node, 'CommaSep')
  const items: ML[] = []
  if (commaSep) {
    for (const c of children(commaSep)) {
      if (c.name === 'ParenInner' || c.name === 'AtomExpr' || c.name.startsWith('Bin') || c.name === 'Expr' || c.name === 'Let' || c.name === 'Match' || c.name === 'Fun' || c.name === 'If' || c.name === 'AppInner') {
        items.push(buildML(c, src))
      }
    }
  }
  if (items.length === 1) {
    return { ...items[0], meta: { ...items[0].meta, parens: true, start: m.start, end: m.end } }
  }
  return mkML({ kind: 'Tuple', items }, { ...m, parens: true })
}

function buildListExpr(node: SyntaxNode, src: string, m: Meta): ML {
  const commaSep = firstChildByName(node, 'CommaSep')
  const items: ML[] = []
  if (commaSep) {
    for (const c of children(commaSep)) {
      if (c.name !== ',' && c.name !== 'LBracket' && c.name !== 'RBracket') {
        items.push(buildML(c, src))
      }
    }
  }
  return mkML({ kind: 'List', items }, m)
}

/* Several rules now accept either `Expr` (the strict meta-let RHS form)
   or `TopExpr` (the delimited-position form that admits juxtaposition
   without parens). Treat both uniformly when walking the parse tree. */
const isExprNode = (c: SyntaxNode) => c.name === 'Expr' || c.name === 'TopExpr'

function buildFun(node: SyntaxNode, src: string, m: Meta): ML {
  const params = childrenByName(node, 'Pattern').map(p => buildPat(p, src))
  const exprs = children(node).filter(isExprNode)
  const body = exprs.length > 0
    ? buildML(exprs[exprs.length - 1], src)
    : mkML({ kind: 'Hole' })
  return mkML({ kind: 'Fun', params, body }, m)
}

function buildMatch(node: SyntaxNode, src: string, m: Meta): ML {
  const exprs = children(node).filter(isExprNode)
  const scrut = exprs.length > 0
    ? buildML(exprs[0], src)
    : mkML({ kind: 'Hole' })
  const arms: { pat: Pat; body: ML }[] = []
  for (const arm of childrenByName(node, 'MatchArm')) {
    const pat = firstChildByName(arm, 'Pattern')
    const armExprs = children(arm).filter(isExprNode)
    arms.push({
      pat: pat ? buildPat(pat, src) : mkPat({ kind: 'PWildcard' }),
      body: armExprs.length > 0
        ? buildML(armExprs[0], src)
        : mkML({ kind: 'Hole' }),
    })
  }
  return mkML({ kind: 'Match', scrut, arms }, m)
}

function buildIf(node: SyntaxNode, src: string, m: Meta): ML {
  const exprs = children(node).filter(isExprNode)
  const get = (i: number): ML =>
    exprs[i] ? buildML(exprs[i], src) : mkML({ kind: 'Hole' })
  return mkML({ kind: 'If', cond: get(0), then_: get(1), else_: get(2) }, m)
}

function buildLet(node: SyntaxNode, src: string, m: Meta): ML {
  // Let { Let_kw Pattern (":" Expr)? "=" TopExpr In_kw TopExpr }
  const patNode = firstChildByName(node, 'Pattern')
  const exprs = children(node).filter(isExprNode)
  const annotation: MLType | null = null
  let rawAnnotation: ML | null = null
  let definition: ML
  let body: ML
  if (exprs.length === 3) {
    rawAnnotation = buildML(exprs[0], src)
    definition = buildML(exprs[1], src)
    body = buildML(exprs[2], src)
  } else if (exprs.length === 2) {
    definition = buildML(exprs[0], src)
    body = buildML(exprs[1], src)
  } else {
    definition = mkML({ kind: 'Hole' })
    body = mkML({ kind: 'Hole' })
  }
  const pat: Pat = patNode
    ? buildPat(patNode, src)
    : mkPat({ kind: 'PVar', name: '_' })
  const binding: LetBinding = {
    pat,
    annotation,
    rawAnnotation,
    definition,
    bindingMeta: metaOf(node),
  }
  return mkML({ kind: 'Let', binding, body }, m)
}

/* === MetaDef and Block building === */

function buildMetaDef(node: SyntaxNode, src: string): MetaDef {
  // MetaItem { (Schema_kw | Coerce_kw)? Identifier (":" Expr)? "=" Expr
  //          | Newtag_kw Tag }
  const isNewtag = !!firstChildByName(node, 'Newtag_kw')
  if (isNewtag) {
    const tagNode = firstChildByName(node, 'Tag')
    const lexeme = tagNode ? text(tagNode, src) : '#_'
    const tag = lexeme.startsWith('#') ? lexeme.slice(1) : lexeme
    return { kind: 'NewtagDef', tag, defMeta: metaOf(node) }
  }
  const isSchema = !!firstChildByName(node, 'Schema_kw')
  const isCoerce = !!firstChildByName(node, 'Coerce_kw')
  const id = firstChildByName(node, 'Identifier')
  const exprs = children(node).filter(c => c.name === 'Expr')
  let rawAnnotation: ML | null = null
  let definition: ML
  if (exprs.length === 2) {
    rawAnnotation = buildML(exprs[0], src)
    definition = buildML(exprs[1], src)
  } else if (exprs.length === 1) {
    definition = buildML(exprs[0], src)
  } else {
    definition = mkML({ kind: 'Hole' })
  }
  const name = id ? text(id, src) : '_'
  if (isSchema || isCoerce) {
    const binding: Binding = {
      pat: name,
      annotation: null,
      rawAnnotation,
      definition,
      bindingMeta: metaOf(node),
    }
    return isSchema
      ? { kind: 'SchemaDef', binding }
      : { kind: 'CoerceDef', binding }
  }
  const pat: Pat = id
    ? mkPat({ kind: 'PVar', name }, metaOf(id))
    : mkPat({ kind: 'PVar', name })
  const binding: LetBinding = {
    pat,
    annotation: null,
    rawAnnotation,
    definition,
    bindingMeta: metaOf(node),
  }
  return { kind: 'LetDef', binding }
}

/* Read a `Tag Identifier Terminator` line: e.g. `#reduction abs-ident-eq`. */
function buildTagLine(node: SyntaxNode, src: string): TagLine {
  const tagNode = firstChildByName(node, 'Tag')
  const idNode = firstChildByName(node, 'Identifier')
  const lex = tagNode ? text(tagNode, src) : '#_'
  return {
    tag: lex.startsWith('#') ? lex.slice(1) : lex,
    target: idNode ? text(idNode, src) : '_',
    lineMeta: metaOf(node),
  }
}

/* Walk a postulate/construct block's children once, collecting Decl and
   TagLine entries into a single `lines` array in source order. */
function buildOLLines(node: SyntaxNode, src: string): OLLine[] {
  const lines: OLLine[] = []
  for (const c of children(node)) {
    if (c.name === 'PostItem') {
      const decl = firstChildByName(c, 'Decl')
      if (decl) lines.push({ kind: 'Decl', ...buildDeclLine(decl, src) })
    } else if (c.name === 'Decl') {
      lines.push({ kind: 'Decl', ...buildDeclLine(c, src) })
    } else if (c.name === 'TagLine') {
      lines.push({ kind: 'Tag', ...buildTagLine(c, src) })
    }
  }
  return lines
}

function buildBlock(node: SyntaxNode, src: string): Block | null {
  switch (node.name) {
    case 'Postulate':
      return {
        kind: 'Postulate',
        postulateMeta: metaOf(node),
        lines: buildOLLines(node, src),
      }
    case 'Construct': {
      // First Identifier child is the schema name
      const id = firstChildByName(node, 'Identifier')
      const schema = id ? text(id, src) : '_'
      const schemaMeta = id ? metaOf(id) : metaOf(node)
      return {
        kind: 'Construct',
        schema,
        schemaMeta,
        lines: buildOLLines(node, src),
      }
    }
    case 'Meta': {
      const defs = childrenByName(node, 'MetaItem').map(m => buildMetaDef(m, src))
      return { kind: 'Meta', defs }
    }
    default:
      return null
  }
}

export function buildProgram(tree: Tree, src: string): Program {
  const blocks: Block[] = []
  const top = tree.topNode
  for (let c = top.firstChild; c; c = c.nextSibling) {
    if (c.name === 'Block') {
      const inner = c.firstChild
      if (inner) {
        const b = buildBlock(inner, src)
        if (b) blocks.push(b)
      }
    }
  }
  return blocks
}
