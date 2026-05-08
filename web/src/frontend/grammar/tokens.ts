import { ContextTracker, ExternalTokenizer } from '@lezer/lr'
// @ts-ignore — generated alongside the parser by lezer-generator
import { LParen, RParen, LBracket, RBracket, Terminator } from './mint.grammar.terms.js'

/* The grammar uses a single external token, `Terminator`, plus a
   bracket-depth context tracker. A run of whitespace containing a
   newline emits Terminator iff:
   - we are at bracket depth 0 (so multi-line forms wrap in `(...)` /
     `[...]` to absorb their newlines via the regular `space` token), AND
   - the parser can currently shift Terminator (which is true at decl
     boundaries but not while a construct is mid-stream, so newlines
     inside `match`, `fun`, `if/then/else` etc. fall through to `space`),
     AND
   - the next non-blank line is NOT indented. An indented continuation
     line (e.g. wrapping a long Decl across multiple lines) is treated
     as part of the previous decl — the whitespace is consumed as
     ordinary `space` and the Decl keeps accumulating Params or its
     type ascription.
   This third guard is what enables multi-line declarations:
       C (arg1 : T1)
         (arg2 : T2)
         : T3
   Everything indented after `C` (at any column > 0) is part of the
   decl. The decl ends when the next column-0 line begins, or EOF. */

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

  // If the next character is part of an indented line (any column > 0
  // measured from the most recent newline within this whitespace run),
  // the line is a continuation of the previous decl — skip Terminator
  // emission and let the regular `space` token consume the whitespace.
  // EOF (-1) doesn't count as indented.
  const nextChar = input.peek(pos)
  if (nextChar !== -1) {
    let lastNlPos = -1
    for (let q = pos - 1; q >= 0; q--) {
      const c = input.peek(q)
      if (c === NL || c === CR) { lastNlPos = q; break }
    }
    const indent = lastNlPos >= 0 ? pos - lastNlPos - 1 : 0
    if (indent > 0) return
  }

  if (stack.canShift(Terminator)) input.acceptToken(Terminator, pos)
})
