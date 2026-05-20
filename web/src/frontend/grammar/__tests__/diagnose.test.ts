import { describe, it, expect } from 'vitest'
// @ts-ignore
import { parser } from '../mint.grammar.js'

function check(code: string): { errs: number; tree: string } {
  const t = parser.parse(code).toString()
  return { errs: (t.match(/⚠/g) || []).length, tree: t }
}

describe('diagnose snippets', () => {
  const cases: Record<string, string> = {
    A: 'postulate\nSort : Sort',
    AAA: 'postulate\nx : y',
    B: 'postulate\nSort : Sort\nU : Sort',
    C: 'postulate\nSort : Sort\nU : Sort\n(eq (A : U) (B : U)) : U',
    D: 'postulate\nU : Sort\n(refl (A : U) (a : A)) : (eq A A a a)',
    E: 'postulate\nD : U\nK : D\n(ap (f : D) (a : D)) : D',
    G: 'postulate\nA : U\n(refl (A : U) (a : A)) : (eq A A a a)',
    H: 'postulate\n(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
    I: 'meta\nfoo = (Ok [body, (refl ret body)])',
    J: 'meta\nfoo = match s with | x => a | _ => b end',
    K: 'meta\nfoo = fun s => match s with | x => x end',
    L: 'meta\nfoo = if a == b then x else y end',
    M: 'meta\nfoo = (a, b, c)',
    N: 'meta\nschema foo = a',
    O: 'postulate\ny : (eq D D x ?)',
    P: 'meta\nfoo = match s with | (a, b, c) => x end',
    Q: 'meta\nfoo = match s with | [a, b] => x end',
    R: 'meta\nfoo = match s with | [(f, [], ret)] => x end',
    S: 'meta\nfoo = match s with | [(f, [], eq l ret ret f body)] => x end',
    T: `meta
schema definition =
  fun s => match s with
  | [(f, [], ret, _)]
      => x
  | _ => (Error "bad")
  end`,
    U: 'meta\nfoo =\n  bar',
    V: 'meta\nfoo = bar',
    W: 'postulate\nx : y\nmeta\nfoo = bar',
    X: 'postulate\nA : B',
    Y: 'meta\nfoo = bar\nbaz = qux',
    Z: 'meta\nfoo = (a b c)\nbaz = qux',
    AA: 'meta\nschema foo = fun s => match s with | x => x end',
    BB: 'postulate\n(eq (A : U)) : U\n(refl (A : U)) : U',
    CC: 'postulate\n(Either (A : U) (B : U)) : U\n(inl (A : U)) : Either',
    DD: 'postulate\nU : Sort\n-- comment\n(Either (A : U)) : U',
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
