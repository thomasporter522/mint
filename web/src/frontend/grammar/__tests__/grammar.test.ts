import { describe, it, expect } from 'vitest'
import { readFileSync, readdirSync } from 'fs'
import { resolve, join } from 'path'
// @ts-ignore — generated module
import { parser } from '../mint.grammar.js'

function tree(code: string): string {
  return parser.parse(code).toString()
}

function findErrors(code: string): { count: number; tree: string } {
  const t = parser.parse(code).toString()
  const matches = t.match(/⚠/g)
  return { count: matches ? matches.length : 0, tree: t }
}

describe('Lezer grammar smoke', () => {
  it('parses a tiny postulate block', () => {
    const code = 'postulate\nsort : sort'
    const t = tree(code)
    expect(t).not.toMatch(/⚠/)  // no error nodes
    expect(t).toMatch(/Document/)
    expect(t).toMatch(/Postulate/)
    expect(t).toMatch(/Item/)
  })

  it('parses multiple decls separated by newlines', () => {
    const code = 'postulate\nSort : Sort\nU : Sort'
    expect(tree(code)).toMatch(/Document/)
  })

  it('parses a function-style decl with params', () => {
    const code = 'postulate\nU : Sort\n(eq (A : U) (B : U)) : U'
    expect(tree(code)).toMatch(/Document/)
  })

  it('parses a meta block with a let', () => {
    const code = 'postulate\nU : Sort\nmeta\nfoo = 42'
    expect(tree(code)).toMatch(/Document/)
  })
})

describe('Lezer grammar on example files', () => {
  const examplesDir = resolve(__dirname, '../../../../../examples')
  const files = readdirSync(examplesDir).filter(f => f.endsWith('.mint'))

  for (const file of files) {
    it(`parses examples/${file} without errors`, () => {
      const code = readFileSync(join(examplesDir, file), 'utf-8')
      const { count, tree: t } = findErrors(code)
      if (count > 0) {
        // Surface the tree on failure for inspection
        console.error(`Tree for ${file}:`, t.slice(0, 1500))
      }
      expect(count).toBe(0)
    })
  }
})
