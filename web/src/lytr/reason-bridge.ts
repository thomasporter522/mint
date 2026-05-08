/* The TS-side processCode pipeline: parse with Lezer, build the AST in
   TypeScript, then hand the AST to OCaml for type-checking, evaluation,
   or printing. Replaces the prior OCaml-only processCode. */

// @ts-ignore — generated module
import { parser } from './grammar/lytr.grammar.js'
import { buildProgram, buildML } from './builder.ts'
import { collectSyntaxErrors } from './syntax-errors.ts'
// @ts-ignore — Melange-compiled module (relative path so Node and Vite agree)
import {
  processProgramJs,
  printTerm as _printTerm,
  printProgramJs,
  printMLJs,
  checkSchemaMLJs,
  evalMLJs,
} from '../../../reason/_build/default/src/output/src/Lytr_api.js'

import type { Term, Error, holeInfo } from './types'
import type { ML } from './ast'

/* Parse a bare ML expression using the grammar's ExpressionTop entry. */
function parseAsExpr(code: string): ML | null {
  const exprParser = parser.configure({ top: 'ExpressionTop' })
  const tree = exprParser.parse(code)
  const top = tree.topNode
  // top is ExpressionTop with one child of kind TopExpr
  let topExpr: any = top.firstChild
  while (topExpr && topExpr.name !== 'TopExpr') topExpr = topExpr.nextSibling
  if (!topExpr) return null
  // TopExpr has one Expr-like child
  const inner = topExpr.firstChild
  if (!inner) return null
  return buildML(inner, code)
}

/* The main pipeline, used by tests, the web linter, and the CLI.
   Parse → collect syntax errors → build AST → run OCaml check →
   merge syntax errors with the kernel's type errors. */
export function processCode(
  code: string,
): {
  errors: Error[]
  holes: [number, holeInfo][]
  inlayHints: [number, string][]
} {
  const tree = parser.parse(code)
  const syntaxErrors = collectSyntaxErrors(tree)
  const prog = buildProgram(tree, code)
  const result = processProgramJs(prog as unknown[])
  return {
    errors: [...syntaxErrors, ...result.errors],
    holes: result.holes,
    inlayHints: result.inlayHints,
  }
}

/* Back-compat alias; same pipeline. */
export const getStaticsFromCode = processCode

export function printTerm(term: Term): string {
  return _printTerm(term)
}

function looksLikeProgram(code: string): boolean {
  const trimmed = code.trim()
  return /^(postulate|meta|construct|end)\b/.test(trimmed)
}

export function parseAndPrint(code: string): string {
  if (looksLikeProgram(code)) {
    const tree = parser.parse(code)
    const prog = buildProgram(tree, code)
    if (prog.length > 0) return printProgramJs(prog as unknown[])
  }
  const ml = parseAsExpr(code)
  if (!ml) return ''
  return printMLJs(ml as unknown)
}

export function checkSchemaCode(
  code: string,
): { ok: boolean; error: string; from: number; to: number } {
  const ml = parseAsExpr(code)
  if (!ml) return { ok: false, error: 'parse error', from: 0, to: 0 }
  return checkSchemaMLJs(ml as unknown)
}

export function evalCode(
  code: string,
): { ok: boolean; value: string; error: string } {
  const ml = parseAsExpr(code)
  if (!ml) return { ok: false, value: '', error: 'parse error' }
  return evalMLJs(ml as unknown)
}
