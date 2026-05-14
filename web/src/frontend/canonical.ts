/* Canonical solver integration.

   Translate a Mint auto-hole (goal + context) into the Canonical IR
   JSON format, invoke the vendored `canonical-compat` binary, and
   verify the returned candidate by source-substitution + re-elaboration.

   The IR format mirrors Canonical's IRType/IRTerm structs in
   `vendor/Canonical/crates/canonical-compat/src/ir.rs`:
     IRType   = { params: (IRType|null)[], lets: IRLet[], codomain: IRTerm }
     IRTerm   = { params: IRVar[], lets: IRLet[], spine: IRSpine }
     IRSpine  = { head: string, args: IRTerm[] }
     IRVar    = { name: string }

   The outer IRType represents Π (context-bindings) . goal.  The
   `params` array holds each context entry's typed schema; the
   `codomain` is the goal term.
*/

import * as fs from 'fs'
import * as path from 'path'
import * as os from 'os'
import * as child_process from 'child_process'
import type { holeInfo } from './reason-bridge.ts'

/* ml AST TAG values from `type cML` declaration in Term.re — match the
   Melange variant tag order. Stable as long as the Reason enum doesn't
   get reordered. */
const TAG = {
  Shard: 0,
  Hole: 1,
  Identifier: 2,
  StringLit: 3,
  Tuple: 4,
  Asc: 5,
  BinOp: 6,
  Ap: 7,
  List: 8,
  Cons: 9,
} as const

type MlNode = { value: any; meta: any }

type IRTerm = { params: IRVar[]; lets: IRLet[]; spine: IRSpine }
type IRType = { params: (IRType | null)[]; lets: (IRType | null)[]; codomain: IRTerm }
type IRSpine = { head: string; args: IRTerm[] }
type IRVar = { name: string }
type IRLet = { var: IRVar; rules: any[] }

/* Walk a Melange cons-cell list (`{hd, tl: ...}` ending in `tl: 0`)
   into a JS array. */
function mlListToArray<T>(cons: any): T[] {
  const out: T[] = []
  let cur = cons
  while (cur && cur !== 0) {
    out.push(cur.hd)
    cur = cur.tl
  }
  return out
}

/* Convert an OL/ml term tree to a Canonical IRTerm spine.  We treat
   the result as a fully-applied head with zero local binders — that's
   the shape Mint OL terms have (lambdas are encoded via combinators,
   not native binders). */
function mlToIRTerm(t: MlNode): IRTerm {
  const v = t.value
  if (!v) return { params: [], lets: [], spine: { head: '?', args: [] } }
  if (v.TAG === TAG.Identifier) {
    return { params: [], lets: [], spine: { head: v._0, args: [] } }
  }
  if (v.TAG === TAG.Ap) {
    const head = v._0
    const args = mlListToArray<MlNode>(v._1)
    const headName = head.value && head.value.TAG === TAG.Identifier ? head.value._0 : '?'
    return {
      params: [],
      lets: [],
      spine: { head: headName, args: args.map(mlToIRTerm) },
    }
  }
  if (v.TAG === TAG.Hole) {
    return { params: [], lets: [], spine: { head: '?', args: [] } }
  }
  if (v.TAG === TAG.Asc) {
    // strip ascription, take the spine
    return mlToIRTerm(v._0)
  }
  return { params: [], lets: [], spine: { head: '?', args: [] } }
}

/* The display form of a context binding is one of:
     atomic:    Asc(Id(name), retType)
     function:  Asc(Ap(Id(name), [Asc(pname, pty), ...]), retType)
   We deconstruct it into (paramSpecs, retType). */
type ParamSpec = { name: string; ty: MlNode }
function decomposeBinding(t: MlNode): { params: ParamSpec[]; ret: MlNode } | null {
  if (!t.value || t.value.TAG !== TAG.Asc) return null
  const lhs = t.value._0
  const ret = t.value._1
  if (lhs.value && lhs.value.TAG === TAG.Identifier) {
    return { params: [], ret }
  }
  if (lhs.value && lhs.value.TAG === TAG.Ap) {
    const args = mlListToArray<MlNode>(lhs.value._1)
    const params: ParamSpec[] = []
    for (const a of args) {
      if (a.value && a.value.TAG === TAG.Asc && a.value._0.value?.TAG === TAG.Identifier) {
        params.push({ name: a.value._0.value._0, ty: a.value._1 })
      } else {
        params.push({ name: '_', ty: a })
      }
    }
    return { params, ret }
  }
  return null
}

/* A context binding's type as an IRType.  We treat retType `sort` as
   a kind — Canonical encodes that with `null` in the params slot of
   the enclosing IRType. */
function bindingToIRType(t: MlNode): IRType | null {
  const dec = decomposeBinding(t)
  if (!dec) return null
  // Each param's type → IRType (recursively).
  const paramTypes = dec.params.map((p) => paramTypeToIRType(p.ty))
  const paramVars: IRVar[] = dec.params.map((p) => ({ name: p.name }))
  return {
    params: paramTypes,
    lets: [],
    codomain: {
      params: paramVars,
      lets: [],
      spine: spineOf(dec.ret),
    },
  }
}

/* Convert a type-expression (an ml term in a type slot) into an
   IRType wrapping it.  Atomic spines become IRType with no params and
   a single-term codomain.  Pure kind (`sort`) becomes null. */
function paramTypeToIRType(t: MlNode): IRType | null {
  if (t.value?.TAG === TAG.Identifier && t.value._0 === 'sort') return null
  return {
    params: [],
    lets: [],
    codomain: { params: [], lets: [], spine: spineOf(t) },
  }
}

function spineOf(t: MlNode): IRSpine {
  const ir = mlToIRTerm(t)
  return ir.spine
}

/* True if `t`'s spine tree mentions a `?` head anywhere — signals an
   incomplete or untranslatable subterm (e.g. an unsolved meta or the
   auto-char itself). Bindings carrying such heads get dropped from
   the Canonical problem rather than handed to the solver as garbage. */
function spineHasHole(s: IRSpine): boolean {
  if (s.head === '?') return true
  return s.args.some(termHasHole)
}
function termHasHole(t: IRTerm): boolean {
  if (spineHasHole(t.spine)) return true
  return false
}
function typeHasHole(t: IRType | null): boolean {
  if (t == null) return false
  if (spineHasHole(t.codomain.spine)) return true
  return t.params.some(typeHasHole)
}

/* Build the outer IRType problem from an auto-hole.  Each context
   entry becomes a (typed) param of the outer Π; the goal becomes
   the codomain spine.  Bindings that don't fully translate (e.g. the
   in-progress self-reference whose retType still mentions `⟐`) are
   dropped so Canonical sees a clean problem. */
export function buildIRProblem(info: holeInfo): IRType {
  const params: (IRType | null)[] = []
  const paramVars: IRVar[] = []
  for (const [name, term] of info.context as unknown as Map<string, MlNode>) {
    const ty = bindingToIRType(term)
    if (ty != null && typeHasHole(ty)) continue
    params.push(ty)
    paramVars.push({ name })
  }
  return {
    params,
    lets: [],
    codomain: {
      params: paramVars,
      lets: [],
      spine: spineOf(info.goal as unknown as MlNode),
    },
  }
}

/* Build an IR problem from a meta-level signature list (same shape
   schemas receive as their outer scope: `List (Term, List (Term, Term),
   Term)`). Used by the `canonical` builtin to ingest a user-assembled
   context. */
export function buildIRFromSignatures(ctxML: MlNode, goalML: MlNode): IRType {
  const params: (IRType | null)[] = []
  const paramVars: IRVar[] = []
  if (ctxML.value && ctxML.value.TAG === TAG.List) {
    const entries = mlListToArray<MlNode>(ctxML.value._0)
    for (const entry of entries) {
      if (!entry.value || entry.value.TAG !== TAG.Tuple) continue
      const items = mlListToArray<MlNode>(entry.value._0)
      if (items.length !== 3) continue
      const [nameT, paramsT, retT] = items
      const name =
        nameT.value && nameT.value.TAG === TAG.Identifier ? nameT.value._0 : '_'
      const psList =
        paramsT.value && paramsT.value.TAG === TAG.List
          ? mlListToArray<MlNode>(paramsT.value._0)
          : []
      const paramSpecs: { name: string; ty: MlNode }[] = []
      for (const p of psList) {
        if (!p.value || p.value.TAG !== TAG.Tuple) continue
        const ppair = mlListToArray<MlNode>(p.value._0)
        if (ppair.length !== 2) continue
        const pn = ppair[0]
        const pty = ppair[1]
        const pname =
          pn.value && pn.value.TAG === TAG.Identifier ? pn.value._0 : '_'
        paramSpecs.push({ name: pname, ty: pty })
      }
      const ty: IRType = {
        params: paramSpecs.map((p) => paramTypeToIRType(p.ty)),
        lets: [],
        codomain: {
          params: paramSpecs.map((p) => ({ name: p.name })),
          lets: [],
          spine: spineOf(retT),
        },
      }
      if (typeHasHole(ty)) continue
      params.push(ty)
      paramVars.push({ name })
    }
  }
  return {
    params,
    lets: [],
    codomain: {
      params: paramVars,
      lets: [],
      spine: spineOf(goalML),
    },
  }
}

/* Resolve `vendor/Canonical/target/release/canonical-compat` regardless
   of whether this module is loaded as an ESM source file (CLI / tests)
   or bundled into a CJS extension. Walks upward from the script's
   directory looking for `vendor/Canonical`. Falls back to CWD-relative
   if nothing is found. */
function findCanonicalDir(): string | null {
  const candidates: string[] = []
  try {
    // ESM context (Node ≥18 with --experimental-strip-types)
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const meta = (import.meta as any) as { url?: string }
    if (meta && typeof meta.url === 'string') {
      candidates.push(path.dirname(new URL(meta.url).pathname))
    }
  } catch {}
  if (typeof __dirname !== 'undefined') candidates.push(__dirname)
  candidates.push(process.cwd())
  for (const start of candidates) {
    let dir = start
    for (let i = 0; i < 10; i++) {
      const candidate = path.join(dir, 'vendor', 'Canonical')
      if (fs.existsSync(candidate)) return candidate
      const next = path.dirname(dir)
      if (next === dir) break
      dir = next
    }
  }
  return null
}
const CANONICAL_DIR = findCanonicalDir()
const CANONICAL_BIN = CANONICAL_DIR
  ? path.join(CANONICAL_DIR, 'target', 'release', 'canonical-compat')
  : null

/* Invoke canonical-compat against a written IR JSON and return the
   single inhabitant line printed on stdout.  Returns null on failure
   (binary missing, timeout, no solution, parse error in output). */
export function runCanonical(problem: IRType, timeoutMs = 5000): string | null {
  if (!CANONICAL_BIN || !fs.existsSync(CANONICAL_BIN)) return null
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mint-canonical-'))
  const leanDir = path.join(tmpDir, 'lean')
  fs.mkdirSync(leanDir, { recursive: true })
  fs.writeFileSync(path.join(leanDir, 'debug.json'), JSON.stringify(problem))
  try {
    const out = child_process.execFileSync(CANONICAL_BIN, [], {
      cwd: tmpDir,
      timeout: timeoutMs,
      encoding: 'utf-8',
      stdio: ['ignore', 'pipe', 'pipe'],
    })
    /* The binary prints: an entropy log, a timestamp, then the
       inhabitant.  We take the last non-empty line that isn't a
       step-count tick. */
    const lines = out.split('\n').map((l) => l.trim()).filter(Boolean)
    for (let i = lines.length - 1; i >= 0; i--) {
      const l = lines[i]
      if (l.startsWith('total:') || l.startsWith('t/s:') || /^[\d.]+$/.test(l) || l.startsWith('entropy')) continue
      return l
    }
    return null
  } catch (_e) {
    return null
  }
}

