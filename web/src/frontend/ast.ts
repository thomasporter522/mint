/* TypeScript mirror of the OCaml AST in reason/src/Term.re. The grammar's
   builder produces values of these types, and the OCaml side decodes them.
   When Term.re changes, this file must be updated in lockstep — there's a
   smoke test that constructs every variant from both sides. */

export type Meta = { parens: boolean; start: number; end: number }

export const defaultMeta: Meta = { parens: false, start: -1, end: -1 }

export type BinOp = 'Eq' | 'Neq' | 'And' | 'Or'

/* A name carrying its own source range. Used wherever the OCaml side
   needs to keep an identifier's position separable from a surrounding
   construct's range (e.g. go-to-def on an OLAp head, on the name of a
   decl, on a declArg's identifier). */
export type StringMeta = { string: string; meta: Meta }

/* === Object-language terms ===
   Identifiers no longer have their own variant — a bare name is a
   zero-arg `OLAp` so every applied form goes through one path. */

export type COL =
  | { kind: 'OLHole' }
  | { kind: 'OLAp'; f: StringMeta; args: OL[] }

export type OL = { value: COL; meta: Meta }

export type DeclArg = {
  declArgName: StringMeta
  declArgType: OL
  declArgMeta: Meta
}

export type DeclLine = {
  declName: StringMeta
  args: DeclArg[]
  retType: OL
  declMeta: Meta
}

/* A tag-line `#tagname constructorname` decorates an existing OL
   binding. It doesn't introduce a name; it records that this tag
   applies to `target`. */
export type TagLine = { tag: string; target: string; lineMeta: Meta }

/* A single line inside a postulate/construct block — either a decl or
   a tag attachment. Replaces the previous parallel `decls`+`tagLines`
   lists so source-order is preserved end-to-end. */
export type OLLine =
  | ({ kind: 'Decl' } & DeclLine)
  | ({ kind: 'Tag' } & TagLine)

/* === Meta-language types === */

export type MLType =
  | { kind: 'MOLTerm'; term: OL }
  | { kind: 'MBool' }
  | { kind: 'MString' }
  | { kind: 'MTag' }
  | { kind: 'MList'; elem: MLType }
  | { kind: 'MResult'; elem: MLType }
  | { kind: 'MTuple'; elems: MLType[] }
  | { kind: 'MArrow'; from: MLType; to: MLType }

/* === Patterns === */

export type CPat =
  | { kind: 'PWildcard' }
  | { kind: 'PVar'; name: string }
  | { kind: 'PString'; value: string }
  | { kind: 'PList'; items: Pat[] }
  | { kind: 'PCons'; head: Pat; tail: Pat }
  | { kind: 'PTuple'; items: Pat[] }
  | { kind: 'POLAp'; head: string; args: Pat[] }

export type Pat = { value: CPat; meta: Meta }

/* === Meta-language expressions === */

export type CML =
  | { kind: 'Hole' }
  | { kind: 'Meta'; id: number }
  | { kind: 'Identifier'; name: string }
  | { kind: 'Ap'; f: ML; args: ML[] }
  | { kind: 'StringLit'; value: string }
  | { kind: 'TagLit'; name: string }
  | { kind: 'Tuple'; items: ML[] }
  | { kind: 'BinOp'; op: BinOp; left: ML; right: ML }
  | { kind: 'List'; items: ML[] }
  | { kind: 'Cons'; head: ML; tail: ML }
  | { kind: 'Fun'; params: Pat[]; body: ML }
  | { kind: 'Match'; scrut: ML; arms: { pat: Pat; body: ML }[] }
  | { kind: 'If'; cond: ML; then_: ML; else_: ML }
  | { kind: 'Let'; binding: LetBinding; body: ML }

export type ML = { value: CML; meta: Meta }

/* let [pat] (: [annotation])? = [definition] — LHS can be any pattern. */
export type LetBinding = {
  pat: Pat
  annotation: MLType | null      // parsed type, if recognized
  rawAnnotation: ML | null       // original type expression for errors
  definition: ML
  bindingMeta: Meta
}

/* Top-level Schema/Coerce defs bind a bare name (no destructuring). */
export type Binding = {
  pat: string
  annotation: MLType | null
  rawAnnotation: ML | null
  definition: ML
  bindingMeta: Meta
}

export type MetaDef =
  | { kind: 'LetDef'; binding: LetBinding }
  | { kind: 'SchemaDef'; binding: Binding }
  | { kind: 'CoerceDef'; binding: Binding }
  | { kind: 'NewtagDef'; tag: string; defMeta: Meta }

/* === Program structure === */

export type Block =
  | { kind: 'Postulate'; postulateMeta: Meta; lines: OLLine[] }
  | { kind: 'Meta'; defs: MetaDef[] }
  | { kind: 'Construct'; schema: string; schemaMeta: Meta; lines: OLLine[] }

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
      value = { kind: 'Hole' }
      break
    case 'OLAp': {
      const mlF: ML = {
        value: { kind: 'Identifier', name: t.value.f.string },
        meta: t.value.f.meta,
      }
      value = { kind: 'Ap', f: mlF, args: t.value.args.map(embedOL) }
      break
    }
  }
  return { value, meta: t.meta }
}
