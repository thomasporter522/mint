// Types for the JS boundary with ReasonML.
// Terms are opaque — only printTerm can inspect them.

export type Term = any

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
