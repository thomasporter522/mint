import { describe, it, expect } from 'vitest'
// @ts-ignore
import { parser } from '../grammar/mint.grammar.js'
import { buildProgram } from '../builder'

function build(code: string) {
  const tree = parser.parse(code)
  return buildProgram(tree, code)
}

describe('TS builder smoke', () => {
  it('parses a tiny postulate block', () => {
    const prog = build('postulate\nSort : Sort\nend')
    expect(prog).toHaveLength(1)
    expect(prog[0].kind).toBe('Postulate')
    if (prog[0].kind === 'Postulate') {
      expect(prog[0].decls).toHaveLength(1)
      expect(prog[0].decls[0].declName).toBe('Sort')
      expect(prog[0].decls[0].retType.value.kind).toBe('OLIdentifier')
    }
  })

  it('parses a function-form decl with params', () => {
    const prog = build('postulate\nU : Sort\n(eq (A : U) (B : U)) : U\nend')
    expect(prog).toHaveLength(1)
    if (prog[0].kind !== 'Postulate') throw new Error('expected Postulate')
    expect(prog[0].decls).toHaveLength(2)
    const eq = prog[0].decls[1]
    expect(eq.declName).toBe('eq')
    expect(eq.params.map(p => p.paramName)).toEqual(['A', 'B'])
  })

  it('parses applied types via juxtaposition', () => {
    const prog = build('postulate\nU : Sort\n(refl (A : U)) : eq A A\nend')
    if (prog[0].kind !== 'Postulate') throw new Error()
    const refl = prog[0].decls[1]
    expect(refl.declName).toBe('refl')
    expect(refl.retType.value.kind).toBe('OLAp')
  })

  it('parses meta let bindings', () => {
    const prog = build('meta\nfoo = bar\nend')
    expect(prog).toHaveLength(1)
    if (prog[0].kind !== 'Meta') throw new Error()
    expect(prog[0].defs).toHaveLength(1)
    expect(prog[0].defs[0].kind).toBe('LetDef')
    expect(prog[0].defs[0].binding.name).toBe('foo')
  })

  it('parses construct blocks', () => {
    const prog = build('construct by enum\nfoo : U\nbar : U\nend')
    if (prog[0].kind !== 'Construct') throw new Error()
    expect(prog[0].schema).toBe('enum')
    expect(prog[0].decls.map(d => d.declName)).toEqual(['foo', 'bar'])
  })

  it('parses match expressions', () => {
    const prog = build('meta\nfoo = match s with | x => a | _ => b end\nend')
    if (prog[0].kind !== 'Meta') throw new Error()
    const def = prog[0].defs[0]
    if (def.binding.rhs.value.kind !== 'Match') throw new Error('expected Match')
    expect(def.binding.rhs.value.arms).toHaveLength(2)
  })
})
