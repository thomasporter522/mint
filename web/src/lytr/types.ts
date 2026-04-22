// Types for the JS boundary with ReasonML.
// Terms are opaque — only printTerm can inspect them.
// Using `unknown` forces callers to go through printTerm rather than
// accidentally relying on the Melange runtime shape.

export type Term = unknown

export interface Error {
  type: string
  message: string
  from: number
  to: number
}

export type Context = Map<string, Term>

export interface holeInfo {
  goal: Term
  context: Context
}
