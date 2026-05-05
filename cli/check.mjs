#!/usr/bin/env node
/* Run with: node --experimental-strip-types cli/check.mjs <file.mint>
   The Makefile's `make check` target wires the right flags. Routes through
   the same `processCode` the web app and tests use, so syntax errors and
   kernel errors surface uniformly. */

import { processCode, printTerm } from '../web/src/lytr/reason-bridge.ts'
import { readFileSync } from 'fs'
import { resolve } from 'path'

const file = process.argv[2]
if (!file) {
  console.error('Usage: mint-check <file.mint>')
  process.exit(1)
}

const filePath = resolve(file)
let code
try {
  code = readFileSync(filePath, 'utf-8')
} catch (e) {
  console.error(`Error reading ${filePath}: ${e.message}`)
  process.exit(1)
}

const { errors, holes } = processCode(code)

function offsetToLineCol(code, offset) {
  if (offset < 0) return null
  let line = 1
  let col = 1
  for (let i = 0; i < offset && i < code.length; i++) {
    if (code[i] === '\n') { line++; col = 1 } else { col++ }
  }
  return { line, col }
}

for (const err of errors) {
  const pos = offsetToLineCol(code, err.from)
  if (pos) {
    console.error(`\x1b[31m${filePath}:${pos.line}:${pos.col}: ${err.message}\x1b[0m`)
  } else {
    console.error(`\x1b[31m${err.message}\x1b[0m`)
  }
}

for (const hole of holes) {
  const pos = offsetToLineCol(code, hole[0])
  const info = hole[1]
  const goal = printTerm(info.goal)
  if (pos) {
    console.log(`\x1b[35m${filePath}:${pos.line}:${pos.col}: ? : ${goal}\x1b[0m`)
  }
  for (const [, term] of info.context) {
    console.log(`  ${printTerm(term)}`)
  }
}

if (errors.length === 0 && holes.length === 0) {
  console.log('\x1b[32m✓ No errors, no holes\x1b[0m')
} else {
  if (errors.length > 0) {
    console.error(`\x1b[31m${errors.length} error${errors.length > 1 ? 's' : ''}\x1b[0m`)
  }
  if (holes.length > 0) {
    console.log(`\x1b[35m${holes.length} hole${holes.length > 1 ? 's' : ''}\x1b[0m`)
  }
}

process.exit(errors.length > 0 ? 1 : 0)
