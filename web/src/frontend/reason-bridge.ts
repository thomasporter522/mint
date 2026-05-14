/* The TS-side processCode pipeline: parse with Lezer, build the AST in
   TypeScript, then hand the AST to OCaml for type-checking, evaluation,
   or printing. Replaces the prior OCaml-only processCode. */

// @ts-ignore — generated module
import { parser } from './grammar/mint.grammar.js'
import { buildProgram, buildML, buildOL } from './builder.ts'
import { collectSyntaxErrors } from './syntax-errors.ts'
import { buildIRProblem, buildIRFromSignatures, runCanonical } from './canonical.ts'
// @ts-ignore — Melange-compiled module (relative path so Node and Vite agree)
import {
  processProgramJs,
  printTerm as _printTerm,
  printProgramJs,
  printMLJs,
  checkSchemaMLJs,
  evalMLJs,
  elaborateProgramJs,
  verifyAutoCandidateJs,
  verifyCandidateInContextJs,
  setCanonicalCallbackJs,
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
  /* ⟐ auto-hole sites that should be sent to Canonical. Same shape as
     `holes`. */
  autoHoles: [number, holeInfo][]
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
  /* Every parsed block's range, regardless of completeness. Used by
     `processCodeWithCanonical` to re-derive `completeBlocks` after
     resolving auto-holes. */
  allBlocks: [number, number][]
} {
  const tree = parser.parse(code)
  const syntaxErrors = collectSyntaxErrors(tree)
  const prog = buildProgram(tree, code)
  const result = processProgramJs(prog as unknown[])
  const allErrors: Error[] = [...syntaxErrors, ...result.errors]
  /* Engine emits each complete block's full source range. Discard any
     block whose range overlaps a real error — warnings don't count as
     errors (e.g. shadowing notices don't break completeness). Syntactic
     errors are filtered here because they live on the bridge side and
     aren't visible to the engine's per-decl completeness logic. */
  const realErrors = allErrors.filter((e) => e.type !== 'warning')
  const rawComplete = result.completeBlocks as unknown as [number, number][]
  const completeBlocks = rawComplete.filter(
    ([from, to]) => !realErrors.some((e) => e.from < to && e.to > from),
  )
  return {
    errors: allErrors,
    holes: result.holes,
    autoHoles: result.autoHoles,
    inlayHints: result.inlayHints,
    definitions: result.definitions,
    completeBlocks,
    allBlocks: (result as any).allBlocks as [number, number][],
  }
}

/* Back-compat alias; same pipeline. */
export const getStaticsFromCode = processCode

export function printTerm(term: Term): string {
  return _printTerm(term)
}

/* Result of resolving one `⟐` auto-hole through Canonical. */
export type AutoResult = {
  offset: number
  candidate: string | null   /* solver output, or null if no solution */
  ok: boolean                /* candidate type-checked at the expected position */
  errors: Error[]            /* errors that landed in the candidate's span */
}

/* Register the bridge as the resolver for the meta-language `canonical`
   builtin: when Eval encounters `canonical(ctx, goal)`, it invokes this
   function with the evaluated ctx (a signature list) and goal as ml
   AST objects, and expects an ml AST `Ok(candidate)` or `Error(msg)`
   back. The implementation: encode to Canonical's IR, shell out to the
   solver, parse the inhabitant, verify it against the supplied
   context, and lift to the result variant. */
/* The output of this callback is fed through `Decode.decodeML` on the
   Reason side, which expects the AST in the *kind-tagged* JSON shape
   the TS builder uses ({value: {kind: ..., ...}, meta: ...}), NOT the
   Melange variant-tag shape (TAG / _0 / _1) that the inputs are
   encoded in. We construct results in kind-tagged form. */
setCanonicalCallbackJs((ctxML: any, goalML: any) => {
  const noMeta = { parens: false, start: -1, end_: -1, ghost: false }
  const mkId = (name: string) => ({
    value: { kind: 'Identifier', name },
    meta: noMeta,
  })
  const mkStr = (s: string) => ({
    value: { kind: 'StringLit', value: s },
    meta: noMeta,
  })
  const mkAp = (f: any, args: any[]) => ({
    value: { kind: 'Ap', f, args },
    meta: noMeta,
  })
  const ok = (candidate: any) => mkAp(mkId('Ok'), [candidate])
  const err = (msg: string) => mkAp(mkId('Error'), [mkStr(msg)])
  try {
    const problem = buildIRFromSignatures(ctxML, goalML)
    const candidate = runCanonical(problem)
    if (candidate == null) return err('canonical: no solution')
    const candidateOL = parseAsExpr(candidate)
    if (!candidateOL) return err('canonical: solver output failed to parse')
    const errs = verifyCandidateInContextJs(ctxML, goalML, candidateOL) as Error[]
    if (errs.length > 0) return err('canonical: candidate did not type-check')
    return ok(candidateOL)
  } catch (e) {
    return err(`canonical: ${(e as Error).message ?? String(e)}`)
  }
})

/* processCode + Canonical orchestration.  For each `⟐` auto-hole in
   `code`, builds a Canonical IR problem from the goal + context,
   shells out to the vendored `canonical-compat` binary, parses the
   returned candidate as a Mint expression, and hands it to the kernel
   for a FOCUSED check: `verifyAutoCandidateJs(offset, candidateOL)`
   runs `checkOLTerm` in the saved (context, expected type) for the
   auto-hole.  No source rewriting, no global re-elaboration.

   Block-completeness is recomputed locally: a block is "complete"
   when no real error overlaps its range AND every hole in it is an
   auto-hole that the focused check accepted. */
export function processCodeWithCanonical(code: string): ReturnType<typeof processCode> & {
  autoResults: Map<number, AutoResult>
} {
  const r = processCode(code)
  const autoResults = new Map<number, AutoResult>()
  for (const [offset, info] of r.autoHoles) {
    const problem = buildIRProblem(info)
    const candidate = runCanonical(problem)
    if (candidate == null) {
      autoResults.set(offset, { offset, candidate: null, ok: false, errors: [] })
      continue
    }
    /* Parse Canonical's textual output as a Mint expression, hand the
       AST to the kernel for a localized check at the auto-hole's saved
       (context, expected). */
    const candidateOL = parseAsExpr(candidate)
    if (!candidateOL) {
      autoResults.set(offset, { offset, candidate, ok: false, errors: [] })
      continue
    }
    const errs = verifyAutoCandidateJs(offset, candidateOL) as Error[]
    autoResults.set(offset, { offset, candidate, ok: errs.length === 0, errors: errs })
  }
  /* Recompute completeBlocks: blocks whose range carries no real
     error AND whose only outstanding holes are now-resolved auto-
     holes. Reason already published every parsed block as
     `allBlocks`; we filter that set here. */
  const resolved = new Set<number>()
  for (const [off, res] of autoResults) if (res.ok) resolved.add(off)
  const surviving = r.holes.filter(([off]) => !resolved.has(off))
  const realErrors = r.errors.filter((e) => e.type !== 'warning')
  // @ts-ignore — allBlocks plumbed through Api but typed loosely here
  const allBlocks: [number, number][] = (r as any).allBlocks ?? []
  const completeBlocks = allBlocks.filter(
    ([from, to]) =>
      !realErrors.some((e) => e.from < to && e.to > from) &&
      !surviving.some(([off]) => off >= from && off < to),
  )
  return { ...r, holes: surviving, completeBlocks, autoResults }
}

function looksLikeProgram(code: string): boolean {
  const trimmed = code.trim()
  return /^(postulate|meta|construct|end)\b/.test(trimmed)
}

/* elaborate(source): parse, run elaboration, return the printed
   elaborated program plus the errors. Used to assert idempotence:
   `elaborate(elaborate(s)).elaborated === elaborate(s).elaborated`
   and same for errors. Syntax errors are folded in alongside the
   engine's type errors so a syntactically invalid input still gets a
   stable (parser-recovered) elaborated string + the union of errors. */
export function elaborate(code: string): {
  elaborated: string
  errors: Error[]
} {
  const tree = parser.parse(code)
  const syntaxErrors = collectSyntaxErrors(tree)
  const prog = buildProgram(tree, code)
  const result = elaborateProgramJs(prog as unknown[]) as {
    elaborated: string
    errors: Error[]
  }
  return {
    elaborated: result.elaborated,
    errors: [...syntaxErrors, ...result.errors],
  }
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
