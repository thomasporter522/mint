/* TypeScript mirror of the OCaml AST in reason/src/Term.re. The grammar's
   builder produces values of these types, and the OCaml side decodes them.
   When Term.re changes, this file must be updated in lockstep — there's a
   smoke test that constructs every variant from both sides. */

export type Meta = { parens: boolean; start: number; end: number }

export const defaultMeta: Meta = { parens: false, start: -1, end: -1 }

export type HoleKind = 'User' | 'Synthesized'
export type BinOp = 'Eq' | 'Neq' | 'And' | 'Or'

/* === Object-language terms ===
   The fragment used inside declaration types: identifiers, application,
   holes. No lambdas, no lists, no matching. */

export type COL =
  | { kind: 'OLHole'; hk: HoleKind }
  | { kind: 'OLIdentifier'; name: string }
  | { kind: 'OLAp'; f: OL; args: OL[] }

export type OL = { value: COL; meta: Meta }

export type Param = {
  paramName: string
  paramType: OL
  paramMeta: Meta
}

export type Decl = {
  declName: string
  params: Param[]
  retType: OL
  declMeta: Meta
}

/* === Meta-language types === */

export type MLType =
  | { kind: 'MTerm' }
  | { kind: 'MSort' }
  | { kind: 'MBool' }
  | { kind: 'MString' }
  | { kind: 'MList'; elem: MLType }
  | { kind: 'MResult'; elem: MLType }
  | { kind: 'MTuple'; elems: MLType[] }
  | { kind: 'MArrow'; from: MLType; to: MLType }

/* === Patterns === */

export type CPat =
  | { kind: 'PWildcard' }
  | { kind: 'PVar'; name: string }
  | { kind: 'PHole' }
  | { kind: 'PString'; value: string }
  | { kind: 'PList'; items: Pat[] }
  | { kind: 'PCons'; head: Pat; tail: Pat }
  | { kind: 'PTuple'; items: Pat[] }
  | { kind: 'PAp'; head: Pat; args: Pat[] }

export type Pat = { value: CPat; meta: Meta }

/* === Meta-language expressions === */

export type CML =
  | { kind: 'Hole'; hk: HoleKind }
  | { kind: 'Identifier'; name: string }
  | { kind: 'StringLit'; value: string }
  | { kind: 'Tuple'; items: ML[] }
  | { kind: 'Asc'; expr: ML; type: ML }
  | { kind: 'BinOp'; op: BinOp; left: ML; right: ML }
  | { kind: 'Ap'; f: ML; args: ML[] }
  | { kind: 'List'; items: ML[] }
  | { kind: 'Cons'; head: ML; tail: ML }
  | { kind: 'Fun'; params: Pat[]; body: ML }
  | { kind: 'Match'; scrut: ML; arms: { pat: Pat; body: ML }[] }
  | { kind: 'If'; cond: ML; then_: ML; else_: ML }
  | { kind: 'Let'; binding: Binding; body: ML }
  | { kind: 'BuilderError' }

export type ML = { value: CML; meta: Meta }

export type Binding = {
  name: string
  annotation: MLType | null      // parsed type, if recognized
  rawAnnotation: ML | null       // original type expression for errors
  rhs: ML
  bindingMeta: Meta
}

export type MetaDef =
  | { kind: 'LetDef'; binding: Binding }
  | { kind: 'SchemaDef'; binding: Binding }

/* === Program structure === */

export type Block =
  | { kind: 'Postulate'; decls: Decl[] }
  | { kind: 'Meta'; defs: MetaDef[] }
  | { kind: 'Construct'; schema: string; decls: Decl[] }

export type Program = Block[]

/* === Constructors === */

export const mkOL = (v: COL, meta: Meta = defaultMeta): OL => ({ value: v, meta })
export const mkML = (v: CML, meta: Meta = defaultMeta): ML => ({ value: v, meta })
export const mkPat = (v: CPat, meta: Meta = defaultMeta): Pat => ({ value: v, meta })

/* Embed an OL term into the ML language, preserving structure. Mirrors
   Term.re's `embedOL`. */
export function embedOL(t: OL): ML {
  let value: CML
  switch (t.value.kind) {
    case 'OLHole':
      value = { kind: 'Hole', hk: t.value.hk }
      break
    case 'OLIdentifier':
      value = { kind: 'Identifier', name: t.value.name }
      break
    case 'OLAp':
      value = { kind: 'Ap', f: embedOL(t.value.f), args: t.value.args.map(embedOL) }
      break
  }
  return { value, meta: t.meta }
}
