#!/usr/bin/env node
/* Re-print every examples/*.mint file through parse → build → print to
   apply the printer's silly-paren-dropping rules and write back the
   cleaner form. Run once with: node --experimental-strip-types cli/clean-examples.mjs */

import { parser } from '../web/src/lytr/grammar/lytr.grammar.js'
import { buildProgram } from '../web/src/lytr/builder.ts'
// @ts-ignore — Melange-compiled module
import { printProgramJs } from '../reason/_build/default/src/output/src/Lytr_api.js'
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
    if (prog.length === 0) {
      // Not a parseable program — leave alone.
      console.log(`  skip ${file} (empty program)`)
      unchanged++
      continue
    }
    const printed = printProgramJs(prog) + '\n'
    if (printed === original) {
      console.log(`  same ${file}`)
      unchanged++
    } else {
      writeFileSync(path, printed)
      console.log(`  CLEAN ${file}`)
      changed++
    }
  } catch (e) {
    console.error(`  ERR ${file}: ${e.message}`)
    errored++
  }
}

console.log(`\nDone: ${changed} cleaned, ${unchanged} unchanged, ${errored} errored.`)
