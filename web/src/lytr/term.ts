import type { PrimaryToken } from './grammar';

export type TermMeta = {parens: boolean, start: number, end: number}

export type CTerm = 
  | { type: 'Shard', token : PrimaryToken}
  | { type: 'Hole', inserted: boolean }
  | { type: 'Identifier', value: string }
  | { type: 'Asc', left: Term, right: Term }
  | { type: 'Ap', fun: Term, args: Term[] }
  | { type: 'Postulate', body: Term[], rest: Term | null }
  | { type: 'Checker', rest: Term | null }
  | { type: 'Construct', by: Term, body: Term[], rest: Term | null }
  | {type: "BUILDER ERROR"}

export type Term = {value : CTerm, meta : TermMeta}

// wrap in default meta
export function meta(t : CTerm) : Term {
  return {value: t, meta: {parens: false, start:-1, end:-1}}
}