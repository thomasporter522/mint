#!/usr/bin/env node
/* Re-print only `postulate` and `construct` blocks of every examples/*.mint
   to apply the printer's silly-paren-dropping rules. `meta` blocks are left
   exactly as the user wrote them — formatting in meta is the user's call.
   Run once with: node --experimental-strip-types cli/clean-examples.mjs */

// @ts-ignore — generated grammar
import { parser } from '../web/src/frontend/grammar/mint.grammar.js'
import { buildProgram } from '../web/src/frontend/builder.ts'
// @ts-ignore — Melange-compiled module
import { printProgramJs } from '../reason/_build/default/src/output/src/Api.js'
import { readFileSync, writeFileSync, readdirSync } from 'fs'
import { resolve, join } from 'path'

const examplesDir = resolve('examples')
const files = readdirSync(examplesDir).filter(f => f.endsWith('.mint'))

let changed = 0
let unchanged = 0
let errored = 0

for (const file of files) {
  const path = join(examplesDir, file)
  const original = readFileSync(path, 'utf-8')
  try {
    const tree = parser.parse(original)
    const prog = buildProgram(tree, original)

    // Walk the Lezer tree's top-level Block children in order. They line up
    // 1:1 with the AST's program[i] because buildProgram iterates the same
    // sequence.
    const blockSpans = []
    for (let c = tree.topNode.firstChild; c; c = c.nextSibling) {
      if (c.name !== 'Block') continue
      const inner = c.firstChild
      if (!inner) continue
      blockSpans.push({ from: c.from, to: c.to, kind: inner.name })
    }
    if (blockSpans.length !== prog.length) {
      throw new Error(`Block count mismatch: ${blockSpans.length} vs ${prog.length}`)
    }

    // Walk the original text, replacing only postulate/construct blocks
    // with their cleaned re-printed form.
    let out = ''
    let cursor = 0
    for (let i = 0; i < blockSpans.length; i++) {
      const s = blockSpans[i]
      out += original.slice(cursor, s.from)
      if (s.kind === 'Postulate' || s.kind === 'Construct') {
        const printed = printProgramJs([prog[i]])
        // Strip just the trailing `end\n`, leaving the `\n` between this
        // block and whatever follows so block boundaries don't run together.
        out += printed.replace(/end\n$/, '')
      } else {
        out += original.slice(s.from, s.to)
      }
      cursor = s.to
    }
    out += original.slice(cursor)

    if (out === original) {
      console.log(`  same  ${file}`)
      unchanged++
    } else {
      writeFileSync(path, out)
      console.log(`  CLEAN ${file}`)
      changed++
    }
  } catch (e) {
    console.error(`  ERR   ${file}: ${e.message}`)
    errored++
  }
}

console.log(`\nDone: ${changed} cleaned, ${unchanged} unchanged, ${errored} errored.`)
