import type { Tree } from '@lezer/common'
import type { Error } from './types'

/* Collect syntax errors from a Lezer parse tree.
   Lezer is error-tolerant: rather than throwing on malformed input it
   inserts nodes whose `type.isError` flag is true. We walk the tree once,
   emit one diagnostic per such node, and dedupe by span (cascading
   recovery sometimes produces several error nodes at the same position).
   Messages are intentionally generic for now — better wording can come
   from grammar-context inspection later. */
export function collectSyntaxErrors(tree: Tree): Error[] {
  const out: Error[] = []
  const seen = new Set<string>()
  tree.iterate({
    enter(node) {
      if (!node.type.isError) return
      const key = `${node.from}:${node.to}`
      if (seen.has(key)) return
      seen.add(key)
      out.push({
        type: 'syntax',
        message: 'Syntax error',
        from: node.from,
        // Zero-width error spans (insertions) widen to a single character
        // so the squiggle is visible in the editor.
        to: node.to === node.from ? node.from + 1 : node.to,
      })
    },
  })
  return out
}
