/* The TS-side processCode pipeline: parse with Lezer, build the AST in
   TypeScript, then hand the AST to OCaml for type-checking, evaluation,
   or printing. Replaces the prior OCaml-only processCode. */

// @ts-ignore — generated module
import { parser } from './grammar/mint.grammar.js'
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
} from '../../../reason/_build/default/src/output/src/Api.js'

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
  /* (offset, label, tooltip) — label may be collapsed to `…` when every
     ghost in the run is solved; tooltip is always the full values. */
  inlayHints: [number, string, string][]
  /* (useFrom, useTo, defFrom, defTo) for each OL identifier reference
     that resolves to an OL binding. */
  definitions: [number, number, number, number][]
  /* (from, to) — the full source range of every block whose every decl
     is complete (hole-free type and witness, no semantic OR syntactic
     errors anywhere in the block, all transitive deps complete). The
     extension renders a ✓ anchored at `from` (the `postulate` /
     `construct` keyword). */
  completeBlocks: [number, number][]
} {
  const tree = parser.parse(code)
  const syntaxErrors = collectSyntaxErrors(tree)
  const prog = buildProgram(tree, code)
  const result = processProgramJs(prog as unknown[])
  const allErrors: Error[] = [...syntaxErrors, ...result.errors]
  /* Engine emits each complete block's full source range. Discard any
     block whose range overlaps an error of any kind — syntactic errors
     in particular live on the bridge side and aren't visible to the
     engine's per-decl completeness logic. */
  const rawComplete = result.completeBlocks as unknown as [number, number][]
  const completeBlocks = rawComplete.filter(
    ([from, to]) => !allErrors.some((e) => e.from < to && e.to > from),
  )
  return {
    errors: allErrors,
    holes: result.holes,
    inlayHints: result.inlayHints,
    definitions: result.definitions,
    completeBlocks,
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
