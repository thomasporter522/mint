/* Walk a Lezer tree, produce an AST mirroring reason/src/Term.re.
   The Lezer tree is positional only (every node has a type and a span);
   actual text is read from the source string. */

import type { SyntaxNode, Tree } from '@lezer/common'
import type {
  Meta, OL, ML, Pat, Decl, Param, Binding, MetaDef, Block, Program, MLType,
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
   AtomExpr context. We narrow the more general expression-tree to OL
   shape (identifiers, application, holes) and replace anything we can't
   represent with a synthesized hole. */

export function buildOL(node: SyntaxNode, src: string): OL {
  const m = metaOf(node)
  switch (node.name) {
    case 'TypeExpr':
    case 'TypeBinary': {
      const c = node.firstChild
      if (!c) return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
      // Single-child wrapper
      if (!c.nextSibling) return buildOL(c, src)
      // For arrow types, etc., we currently degrade to a synthesized hole.
      // The semantics of arrow types in OL position is rare; revisit when
      // examples need it.
      return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
    }
    case 'TypeApp': {
      const cs = children(node)
      if (cs.length === 0) return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
      const head = buildOL(cs[0], src)
      const args = cs.slice(1).map(c => buildOL(c, src))
      return mkOL({ kind: 'OLAp', f: head, args }, m)
    }
    case 'TypeAtom':
    case 'AtomExpr':
    case 'ParenInner': {
      const c = node.firstChild
      if (!c) return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
      if (c.name === 'LParen' || c.name === 'LBracket') {
        // Parenthesized — recurse into the inner expr (skip LParen/RParen).
        // ParenExpr children: LParen, CommaSep<Expr>?, RParen
        // For OL, we ignore tuples and just take the first inner expr.
        const inner = c.nextSibling
        if (!inner || inner.name === 'RParen' || inner.name === 'RBracket') {
          return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
        }
        const result = buildOL(inner, src)
        // Extend start/end across the parens so anchors (e.g. inlay hints
        // before this term) and diagnostics for the whole expression cover
        // the parens too.
        return { ...result, meta: { ...result.meta, parens: true, start: m.start, end: m.end } }
      }
      return buildOL(c, src)
    }
    case 'Identifier':
      return mkOL({ kind: 'OLIdentifier', name: text(node, src) }, m)
    case 'Hole':
      return mkOL({ kind: 'OLHole', hk: 'User' }, m)
    case 'Wildcard':
      return mkOL({ kind: 'OLHole', hk: 'User' }, m)  // Wildcard in OL → hole
    case 'AppInner': {
      const cs = children(node)
      if (cs.length === 0) return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
      const head = buildOL(cs[0], src)
      const args = cs.slice(1).map(c => buildOL(c, src))
      return mkOL({ kind: 'OLAp', f: head, args }, m)
    }
    case 'CommaSep':
      // Single element passes through; multiple = tuple, not representable in OL.
      const first = node.firstChild
      if (!first) return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
      return buildOL(first, src)
    default:
      return mkOL({ kind: 'OLHole', hk: 'Synthesized' }, m)
  }
}

/* === Param and Decl === */

function buildParams(node: SyntaxNode, src: string): Param[] {
  // Param { LParen Identifier+ ":" TypeExpr RParen }
  // A grouped form like `(l1 l2 : level)` expands into multiple Param
  // records, each sharing the same paramType — semantically equivalent
  // to `(l1 : level) (l2 : level)`. paramMeta points at the whole
  // group so go-to-def / inlay anchors look reasonable; nameMeta is
  // per-identifier so clicking on `l1` jumps to `l1`.
  const ids = childrenByName(node, 'Identifier')
  const ty = firstChildByName(node, 'TypeExpr')
  const paramType = ty ? buildOL(ty, src) : mkOL({ kind: 'OLHole', hk: 'Synthesized' })
  const groupMeta = metaOf(node)
  if (ids.length === 0) {
    return [{
      paramName: '_',
      paramType,
      paramMeta: groupMeta,
      nameMeta: groupMeta,
    }]
  }
  return ids.map(id => ({
    paramName: text(id, src),
    paramType,
    paramMeta: groupMeta,
    nameMeta: metaOf(id),
  }))
}

function buildDecl(node: SyntaxNode, src: string): Decl {
  // Decl { ItemHead (":" TypeExpr)? }
  // ItemHead { Identifier Param* | LParen Identifier Param* RParen }
  const head = firstChildByName(node, 'ItemHead')
  const ty = firstChildByName(node, 'TypeExpr')
  let name = '_'
  let params: Param[] = []
  let nameMeta: Meta = metaOf(node)
  if (head) {
    const hid = firstChildByName(head, 'Identifier')
    if (hid) {
      name = text(hid, src)
      nameMeta = metaOf(hid)
    }
    params = childrenByName(head, 'Param').flatMap(p => buildParams(p, src))
  }
  const retType = ty
    ? buildOL(ty, src)
    : mkOL({ kind: 'OLHole', hk: 'Synthesized' })
  return { declName: name, params, retType, declMeta: metaOf(node), nameMeta }
}

/* === Pattern building === */

export function buildPat(node: SyntaxNode, src: string): Pat {
  const m = metaOf(node)
  switch (node.name) {
    case 'Pattern': {
      const c = node.firstChild
      if (!c) return mkPat({ kind: 'PHole' }, m)
      return buildPat(c, src)
    }
    case 'PatBinary': {
      // Pattern :: Pattern (cons). Children: [Pattern, "::", Pattern].
      const cs = children(node).filter(c => c.name === 'Pattern')
      if (cs.length >= 2) {
        return mkPat({ kind: 'PCons', head: buildPat(cs[0], src), tail: buildPat(cs[1], src) }, m)
      }
      return mkPat({ kind: 'PHole' }, m)
    }
    case 'PatApp': {
      const cs = children(node)
      if (cs.length === 0) return mkPat({ kind: 'PHole' }, m)
      const head = buildPat(cs[0], src)
      const args = cs.slice(1).map(c => buildPat(c, src))
      return mkPat({ kind: 'PAp', head, args }, m)
    }
    case 'PatAtom': {
      const c = node.firstChild
      if (!c) return mkPat({ kind: 'PHole' }, m)
      if (c.name === 'LParen') return buildPatParens(node, src, m)
      if (c.name === 'LBracket') return buildPatList(node, src, m)
      return buildPat(c, src)
    }
    case 'Identifier':
      return mkPat({ kind: 'PVar', name: text(node, src) }, m)
    case 'Wildcard':
      return mkPat({ kind: 'PWildcard' }, m)
    case 'Hole':
      return mkPat({ kind: 'PHole' }, m)
    case 'StringLit': {
      const raw = text(node, src)
      return mkPat({ kind: 'PString', value: raw.slice(1, -1) }, m)
    }
    default:
      return mkPat({ kind: 'PHole' }, m)
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
      if (!c) return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
      return buildML(c, src)
    }
    case 'BinaryExpr':
    case 'BinaryInner':
    case 'TopBinaryExpr':
      return buildBinary(node, src)
    case 'TopExpr': {
      const c = node.firstChild
      if (!c) return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
      return buildML(c, src)
    }
    case 'AppInner': {
      const cs = children(node)
      if (cs.length === 0) return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
      const head = buildML(cs[0], src)
      const args = cs.slice(1).map(c => buildML(c, src))
      return mkML({ kind: 'Ap', f: head, args }, m)
    }
    case 'AtomExpr':
    case 'ParenInner': {
      const c = node.firstChild
      if (!c) return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
      if (c.name === 'LParen') return buildParenExpr(node, src, m)
      if (c.name === 'LBracket') return buildListExpr(node, src, m)
      return buildML(c, src)
    }
    case 'Identifier':
      return mkML({ kind: 'Identifier', name: text(node, src) }, m)
    case 'Hole':
      return mkML({ kind: 'Hole', hk: 'User' }, m)
    case 'Wildcard':
      // _ in ML expression position — treated as a hole
      return mkML({ kind: 'Hole', hk: 'User' }, m)
    case 'StringLit': {
      const raw = text(node, src)
      return mkML({ kind: 'StringLit', value: raw.slice(1, -1) }, m)
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
      return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
  }
}

function buildBinary(node: SyntaxNode, src: string): ML {
  const cs = children(node)
  // Find the operator child (a literal token). Children layout:
  //   Expr <op> Expr
  if (cs.length < 3) return mkML({ kind: 'Hole', hk: 'Synthesized' }, metaOf(node))
  const left = buildML(cs[0], src)
  const opNode = cs[1]
  const right = buildML(cs[2], src)
  const opText = text(opNode, src)
  const m = metaOf(node)
  switch (opText) {
    case '->':
      // Build as Ap(Identifier "->", [left, right]) — Print.printML round-trips
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
      return mkML({ kind: 'Asc', expr: left, type: right }, m)
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
      return mkML({ kind: 'Hole', hk: 'Synthesized' }, m)
  }
}

function buildParenExpr(node: SyntaxNode, src: string, m: Meta): ML {
  // (CommaSep<ParenInner>)?
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

function buildFun(node: SyntaxNode, src: string, m: Meta): ML {
  const params = childrenByName(node, 'Pattern').map(p => buildPat(p, src))
  // The body is the last Expr child (after the => token)
  const exprs = children(node).filter(c => c.name === 'Expr')
  const body = exprs.length > 0
    ? buildML(exprs[exprs.length - 1], src)
    : mkML({ kind: 'Hole', hk: 'Synthesized' })
  return mkML({ kind: 'Fun', params, body }, m)
}

function buildMatch(node: SyntaxNode, src: string, m: Meta): ML {
  const exprs = children(node).filter(c => c.name === 'Expr')
  const scrut = exprs.length > 0
    ? buildML(exprs[0], src)
    : mkML({ kind: 'Hole', hk: 'Synthesized' })
  const arms: { pat: Pat; body: ML }[] = []
  for (const arm of childrenByName(node, 'MatchArm')) {
    const pat = firstChildByName(arm, 'Pattern')
    const armExprs = children(arm).filter(c => c.name === 'Expr')
    arms.push({
      pat: pat ? buildPat(pat, src) : mkPat({ kind: 'PWildcard' }),
      body: armExprs.length > 0
        ? buildML(armExprs[0], src)
        : mkML({ kind: 'Hole', hk: 'Synthesized' }),
    })
  }
  return mkML({ kind: 'Match', scrut, arms }, m)
}

function buildIf(node: SyntaxNode, src: string, m: Meta): ML {
  const exprs = children(node).filter(c => c.name === 'Expr')
  const get = (i: number): ML =>
    exprs[i] ? buildML(exprs[i], src) : mkML({ kind: 'Hole', hk: 'Synthesized' })
  return mkML({ kind: 'If', cond: get(0), then_: get(1), else_: get(2) }, m)
}

function buildLet(node: SyntaxNode, src: string, m: Meta): ML {
  // Let { Let_kw Identifier (":" Expr)? "=" Expr In_kw Expr }
  const id = firstChildByName(node, 'Identifier')
  const exprs = children(node).filter(c => c.name === 'Expr')
  // Heuristic: if 3 exprs, the first is annotation, second is rhs, third is body.
  // If 2 exprs, no annotation: first is rhs, second is body.
  let annotation: MLType | null = null
  let rawAnnotation: ML | null = null
  let rhs: ML
  let body: ML
  if (exprs.length === 3) {
    rawAnnotation = buildML(exprs[0], src)
    rhs = buildML(exprs[1], src)
    body = buildML(exprs[2], src)
  } else if (exprs.length === 2) {
    rhs = buildML(exprs[0], src)
    body = buildML(exprs[1], src)
  } else {
    rhs = mkML({ kind: 'Hole', hk: 'Synthesized' })
    body = mkML({ kind: 'Hole', hk: 'Synthesized' })
  }
  const binding: Binding = {
    name: id ? text(id, src) : '_',
    annotation,
    rawAnnotation,
    rhs,
    bindingMeta: metaOf(node),
  }
  return mkML({ kind: 'Let', binding, body }, m)
}

/* === MetaDef and Block building === */

function buildMetaDef(node: SyntaxNode, src: string): MetaDef {
  // MetaItem { Schema_kw? Identifier (":" Expr)? "=" Expr }
  const isSchema = !!firstChildByName(node, 'Schema_kw')
  const id = firstChildByName(node, 'Identifier')
  const exprs = children(node).filter(c => c.name === 'Expr')
  let rawAnnotation: ML | null = null
  let rhs: ML
  if (exprs.length === 2) {
    rawAnnotation = buildML(exprs[0], src)
    rhs = buildML(exprs[1], src)
  } else if (exprs.length === 1) {
    rhs = buildML(exprs[0], src)
  } else {
    rhs = mkML({ kind: 'Hole', hk: 'Synthesized' })
  }
  const binding: Binding = {
    name: id ? text(id, src) : '_',
    annotation: null,
    rawAnnotation,
    rhs,
    bindingMeta: metaOf(node),
  }
  return isSchema ? { kind: 'SchemaDef', binding } : { kind: 'LetDef', binding }
}

function buildBlock(node: SyntaxNode, src: string): Block | null {
  switch (node.name) {
    case 'Postulate': {
      const decls = childrenByName(node, 'PostItem')
        .map(p => firstChildByName(p, 'Decl'))
        .filter((d): d is SyntaxNode => d !== null)
        .map(d => buildDecl(d, src))
      return { kind: 'Postulate', decls }
    }
    case 'Construct': {
      // First Identifier child is the schema name
      const id = firstChildByName(node, 'Identifier')
      const schema = id ? text(id, src) : '_'
      const schemaMeta = id ? metaOf(id) : metaOf(node)
      const decls = childrenByName(node, 'PostItem')
        .map(p => firstChildByName(p, 'Decl'))
        .filter((d): d is SyntaxNode => d !== null)
        .map(d => buildDecl(d, src))
      return { kind: 'Construct', schema, schemaMeta, decls }
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
