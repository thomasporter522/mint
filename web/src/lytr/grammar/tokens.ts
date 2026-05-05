import { ContextTracker, ExternalTokenizer } from '@lezer/lr'
// @ts-ignore — generated alongside the parser by lezer-generator
import { LParen, RParen, LBracket, RBracket, Terminator } from './lytr.grammar.terms.js'

/* The grammar uses a single external token, `Terminator`, plus a
   bracket-depth context tracker. A run of whitespace containing a
   newline emits Terminator iff:
   - we are at bracket depth 0 (so multi-line forms wrap in `(...)` /
     `[...]` to absorb their newlines via the regular `space` token), AND
   - the parser can currently shift Terminator (which is true at decl
     boundaries but not while a construct is mid-stream, so newlines
     inside `match`, `fun`, `if/then/else` etc. fall through to `space`).
   This second guard is what makes meta blocks effectively
   whitespace-insensitive while keeping postulate/construct newline-
   separated. */

type Ctx = { depth: number }

export const blockContext = new ContextTracker<Ctx>({
  start: { depth: 0 },
  shift(ctx, term) {
    if (term === LParen || term === LBracket) return { depth: ctx.depth + 1 }
    if (term === RParen || term === RBracket) return { depth: Math.max(0, ctx.depth - 1) }
    return ctx
  },
  hash(ctx) { return ctx.depth },
})

const NL = 10
const CR = 13
const SP = 32
const TAB = 9

export const terminatorTokenizer = new ExternalTokenizer((input, stack) => {
  const first = input.peek(0)
  if (first !== NL && first !== CR && first !== SP && first !== TAB) return

  let pos = 0
  let sawNewline = false
  for (;;) {
    const c = input.peek(pos)
    if (c === NL || c === CR) { sawNewline = true; pos++ }
    else if (c === SP || c === TAB) pos++
    else break
  }
  if (!sawNewline) return

  const ctx = stack.context as Ctx
  if (ctx.depth !== 0) return
  if (stack.canShift(Terminator)) input.acceptToken(Terminator, pos)
})
