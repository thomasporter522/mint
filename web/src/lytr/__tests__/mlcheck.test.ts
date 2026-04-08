import { describe, it, expect } from 'vitest';
// @ts-ignore
import { checkSchemaCode } from '@reason/Lytr_api.js';

type MLResult = { ok: boolean; error: string; from: number; to: number };

const check = (code: string): MLResult => checkSchemaCode(code) as MLResult;
const ok = (code: string) => expect(check(code).ok).toBe(true);
const fails = (code: string, msg?: string) => {
  const r = check(code);
  expect(r.ok).toBe(false);
  if (msg) expect(r.error).toContain(msg);
};

/* ------------------------------------------------------------------ */
/*  Schema type: List Signature -> Result (List Term)                  */
/*  Signature = (List (String, Term), Term)                            */
/* ------------------------------------------------------------------ */

describe('ML type checker: basic expressions', () => {
  it('accepts a lambda with correct schema type', () => {
    ok('fun s => (Ok [])');
  });

  it('accepts a lambda returning Error', () => {
    ok('fun s => (Error "bad")');
  });

  it('rejects a bare identifier (not a function)', () => {
    // A bare identifier has type Term, not the schema function type
    fails('x');
  });

  it('rejects wrong return type', () => {
    // Returning a string instead of Result (List Term)
    fails('fun s => "hello"');
  });
});

describe('ML type checker: pattern matching', () => {
  it('accepts match with list patterns', () => {
    ok('fun s => match s with | _ => (Ok []) end');
  });

  it('accepts match with pair patterns in list', () => {
    ok('fun s => match s with | [(?params, ?ret)] => (Ok []) | _ => (Error "bad") end');
  });

  it('accepts match on scrutinee with pipe branches', () => {
    ok('fun s => match s with | [] => (Error "empty") | _ => (Ok []) end');
  });
});

describe('ML type checker: OL patterns', () => {
  it('accepts OL term patterns with meta-variables', () => {
    ok('fun s => match s with | [([(?x, ?t)], ?ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });
});

describe('ML type checker: if/then/else', () => {
  it('accepts if/then/else returning Result', () => {
    // if is parsed as Ap(if, [cond, then, thenBranch, else, elseBranch])
    // For now this should at least not crash
    ok('fun s => (if s then (Ok []) else (Error "bad"))');
  });
});

describe('ML type checker: the full schema definition example', () => {
  it('type-checks the definition schema from ML.md', () => {
    const code = [
      'fun s => match s with',
      '| [([(?x, ?t)], ?ret),',
      '   ([(?x_eq, eq ?t ?t ?body)], _)]',
      '    => (Ok [body, (refl t body)])',
      '| _ =>',
      '  if (List length s != two)',
      '  then (Error "definition declarations must have length 2")',
      '  else (Error "invalid declaration")',
      'end',
    ].join('\n');
    const r = check(code);
    if (!r.ok) {
      console.log('ML check error:', r.error, 'at', r.from, '-', r.to);
    }
    expect(r.ok).toBe(true);
  });
});
