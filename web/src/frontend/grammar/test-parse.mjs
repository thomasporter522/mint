// Quick smoke test: parse a small input and dump the tree.
import { LRParser } from '@lezer/lr'
import { parser } from './mint.grammar.js'
import { newlineTerminator, bracketDepth } from './tokens.ts'

const samples = [
  `postulate
sort : sort
end
`,
  `postulate
Sort : Sort
U : Sort
(eq (A : U) (B : U) (a : A) (b : B)) : U
end
`,
  `postulate
Sort : Sort
end

meta
foo = 42
end
`,
]

for (const code of samples) {
  console.log('--- INPUT ---')
  console.log(code)
  console.log('--- TREE ---')
  try {
    const tree = parser.parse(code)
    console.log(tree.toString())
  } catch (e) {
    console.log('ERROR:', e.message)
  }
  console.log()
}
