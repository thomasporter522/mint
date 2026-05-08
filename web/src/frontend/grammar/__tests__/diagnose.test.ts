import { describe, it, expect } from 'vitest'
// @ts-ignore
import { parser } from '../mint.grammar.js'

function check(code: string): { errs: number; tree: string } {
  const t = parser.parse(code).toString()
  return { errs: (t.match(/⚠/g) || []).length, tree: t }
}

describe('diagnose snippets', () => {
  const cases: Record<string, string> = {
    A: 'postulate\nSort : Sort\nend',
    AAA: 'postulate\nx : y\nend',
    B: 'postulate\nSort : Sort\nU : Sort\nend',
    C: 'postulate\nSort : Sort\nU : Sort\n(eq (A : U) (B : U)) : U\nend',
    D: 'postulate\nU : Sort\n(refl (A : U) (a : A)) : (eq A A a a)\nend',
    E: 'postulate\nD : U\nK : D\n(ap (f : D) (a : D)) : D\nend',
    G: 'postulate\nA : U\n(refl (A : U) (a : A)) : (eq A A a a)\nend',
    H: 'postulate\n(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)\nend',
    I: 'meta\nfoo = (Ok [body, (refl ret body)])\nend',
    J: 'meta\nfoo = match s with | x => a | _ => b end\nend',
    K: 'meta\nfoo = fun s => match s with | x => x end\nend',
    L: 'meta\nfoo = if a == b then x else y end\nend',
    M: 'meta\nfoo = (a, b, c)\nend',
    N: 'meta\nschema foo = a\nend',
    O: 'postulate\ny : (eq D D x ?)\nend',
    P: 'meta\nfoo = match s with | (a, b, c) => x end\nend',
    Q: 'meta\nfoo = match s with | [a, b] => x end\nend',
    R: 'meta\nfoo = match s with | [(f, [], ret)] => x end\nend',
    S: 'meta\nfoo = match s with | [(f, [], eq l ret ret f body)] => x end\nend',
    T: `meta
schema definition =
  fun s => match s with
  | [(f, [], ret)]
      => x
  | _ => (Error "bad")
  end
end`,
    U: 'meta\nfoo =\n  bar\nend',
    V: 'meta\nfoo = bar\nend',
    W: 'postulate\nx : y\nmeta\nfoo = bar\nend',
    X: 'postulate\nA : B\nend',
    Y: 'meta\nfoo = bar\nbaz = qux\nend',
    Z: 'meta\nfoo = (a b c)\nbaz = qux\nend',
    AA: 'meta\nschema foo = fun s => match s with | x => x end\nend',
    BB: 'postulate\n(eq (A : U)) : U\n(refl (A : U)) : U\nend',
    CC: 'postulate\n(Either (A : U) (B : U)) : U\n(inl (A : U)) : Either\nend',
    DD: 'postulate\nU : Sort\n-- comment\n(Either (A : U)) : U\nend',
  }
  for (const [name, code] of Object.entries(cases)) {
    it(`[${name}] parses ${JSON.stringify(code).slice(0, 50)}`, () => {
      const { errs, tree } = check(code)
      if (errs > 0) {
        throw new Error(`${errs} errors\nTREE: ${tree}`)
      }
      expect(errs).toBe(0)
    })
  }
})
