import { parser } from './lytr.grammar.js'

const samples = {
  G: 'postulate\nA : U\n(refl (A : U) (a : A)) : (eq A A a a)\n(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)\nend',
  H: 'postulate\n(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)\nend',
  I: 'meta\nfoo = (Ok [body, (refl ret body)])\nend',
  J: 'meta\nfoo = match s with | x => 1 | _ => 2 end\nend',
  K: 'meta\nfoo = fun s => match s with | x => 1 end\nend',
  L: 'meta\nfoo = if a == b then x else y end\nend',
  M: 'meta\nfoo = (1, 2, 3)\nend',
  N: 'meta\nschema foo = 42\nend',
}

for (const [k, code] of Object.entries(samples)) {
  const t = parser.parse(code).toString()
  const errs = (t.match(/⚠/g) || []).length
  console.log(`[${k}] errs=${errs}`)
  if (errs > 0) {
    console.log(`  CODE: ${JSON.stringify(code)}`)
    console.log(`  TREE: ${t}`)
  }
}
