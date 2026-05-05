import { describe, it } from 'vitest'
import { readFileSync } from 'fs'
import { resolve } from 'path'
// @ts-ignore
import { parser } from '../lytr.grammar.js'

/* Parse a file, find the first ⚠ error position, and dump a window of source
   around it along with the parse tree slice. */

function findFirstError(file: string) {
  const code = readFileSync(resolve(__dirname, '../../../../../examples', file), 'utf-8')
  const tree = parser.parse(code)
  let firstErrPos = -1
  tree.iterate({
    enter(node) {
      if (node.type.isError && firstErrPos === -1) {
        firstErrPos = node.from
      }
    },
  })
  if (firstErrPos === -1) {
    console.log(`${file}: no errors`)
    return
  }
  // Dump source window
  const start = Math.max(0, firstErrPos - 80)
  const end = Math.min(code.length, firstErrPos + 80)
  const before = code.slice(start, firstErrPos)
  const after = code.slice(firstErrPos, end)
  console.log(`\n=== ${file} (first error at offset ${firstErrPos}) ===`)
  console.log(before + '⚠HERE⚠' + after)
}

describe('find first error', () => {
  for (const f of ['universe-levels.mint', 'definition.mint', 'enum-coprod-generic.mint', 'MATH.mint']) {
    it(`reports first error in ${f}`, () => {
      const code = readFileSync(resolve(__dirname, '../../../../../examples', f), 'utf-8')
      const tree = parser.parse(code)
      let firstErrPos = -1
      tree.iterate({
        enter(node) {
          if (node.type.isError && firstErrPos === -1) firstErrPos = node.from
        },
      })
      if (firstErrPos === -1) return
      const start = Math.max(0, firstErrPos - 80)
      const end = Math.min(code.length, firstErrPos + 80)
      const snippet = code.slice(start, firstErrPos) + '⟦HERE⟧' + code.slice(firstErrPos, end)
      throw new Error(`first error at offset ${firstErrPos}: ${JSON.stringify(snippet)}`)
    })
  }
})
