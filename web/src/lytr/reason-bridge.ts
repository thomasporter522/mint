// Bridge module: adapts ReasonML compiled output to the TypeScript interface
// expected by App.tsx

// @ts-ignore - Melange compiled module
import { processCode as _processCode, printTerm as _printTerm } from '@reason/Lytr_api.js';

import type { Term, Error, holeInfo } from './types';

// The combined pipeline: replaces lex -> parse -> build -> getStatics
export function getStaticsFromCode(code: string): { errors: Error[], holes: [Number, holeInfo][] } {
  const result = _processCode(code);
  return {
    errors: result.errors,
    holes: result.holes,
  };
}

// printTerm operates on opaque ReasonML terms
export function printTerm(term: Term): string {
  return _printTerm(term);
}
