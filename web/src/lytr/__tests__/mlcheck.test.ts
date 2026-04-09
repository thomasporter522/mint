import { describe, it, expect } from 'vitest';
// @ts-ignore
import { checkSchemaCode } from '@reason/Lytr_api.js';

type MLResult = { ok: boolean; error: string; from: number; to: number };

const check = (code: string): MLResult => checkSchemaCode(code) as MLResult;
const ok = (code: string) => {
  const r = check(code);
  if (!r.ok) console.log('Unexpected error:', r.error, 'at', r.from, '-', r.to);
  expect(r.ok).toBe(true);
};
const fails = (code: string, msg?: string) => {
  const r = check(code);
  expect(r.ok).toBe(false);
  if (msg) expect(r.error).toContain(msg);
};

/* All schemas have type: List Signature -> Result (List Term)
   where Signature = (List (String, Term), Term) */

/* ------------------------------------------------------------------ */
/*  Basic lambda structure                                             */
/* ------------------------------------------------------------------ */

describe('ML type checker: basic lambda', () => {
  it('accepts a lambda returning Ok []', () => {
    ok('fun s => (Ok [])');
  });

  it('accepts a lambda returning Error', () => {
    ok('fun s => (Error "bad")');
  });

  it('rejects a bare identifier (not a function)', () => {
    fails('x');
  });

  it('rejects wrong return type — string instead of Result', () => {
    fails('fun s => "hello"');
  });

  it('rejects lambda returning bare list (not wrapped in Ok)', () => {
    fails('fun s => []');
  });

  it('rejects lambda returning bare Term', () => {
    fails('fun s => x');
  });
});

/* ------------------------------------------------------------------ */
/*  Ok and Error                                                       */
/* ------------------------------------------------------------------ */

describe('ML type checker: Ok/Error', () => {
  it('Ok wraps a list of terms', () => {
    ok('fun s => (Ok [x, y, z])');
  });

  it('Ok with single element list', () => {
    ok('fun s => (Ok [x])');
  });

  it('Error requires a string argument', () => {
    ok('fun s => (Error "something went wrong")');
  });

  it('Error rejects non-string argument', () => {
    fails('fun s => (Error x)', 'Expected String');
  });

  it('Ok rejects non-list argument', () => {
    fails('fun s => (Ok x)', 'Expected List');
  });
});

/* ------------------------------------------------------------------ */
/*  Pattern matching                                                   */
/* ------------------------------------------------------------------ */

describe('ML type checker: pattern matching', () => {
  it('accepts match with wildcard', () => {
    ok('fun s => match s with | _ => (Ok []) end');
  });

  it('accepts match with variable pattern', () => {
    ok('fun s => match s with | x => (Ok []) end');
  });

  it('accepts match with list patterns', () => {
    ok('fun s => match s with | [] => (Error "empty") | _ => (Ok []) end');
  });

  it('accepts match with pair patterns in list', () => {
    ok('fun s => match s with | [(?params, ?ret)] => (Ok []) | _ => (Error "bad") end');
  });

  it('accepts match with multiple branches', () => {
    ok('fun s => match s with | [] => (Error "empty") | [_] => (Ok []) | _ => (Error "too many") end');
  });

  it('rejects branch returning wrong type', () => {
    fails('fun s => match s with | _ => "wrong" end');
  });

  it('rejects mismatched branch types', () => {
    // First branch returns Result, second returns string
    fails('fun s => match s with | [] => (Ok []) | _ => "wrong" end');
  });
});

/* ------------------------------------------------------------------ */
/*  OL patterns in match                                               */
/* ------------------------------------------------------------------ */

describe('ML type checker: OL patterns', () => {
  it('accepts OL constructor pattern with meta-variables', () => {
    ok('fun s => match s with | [([(?x, ?t)], ?ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });

  it('binds meta-variables for use in body', () => {
    // ?t is bound in pattern, used in Ok [t] in body
    ok('fun s => match s with | [([(?x, ?t)], ?ret)] => (Ok [t]) | _ => (Error "bad") end');
  });

  it('binds meta-variables from OL application patterns', () => {
    // eq ?t ?t ?body binds t and body at type Term
    ok('fun s => match s with | [([(?x, eq ?t ?body)], _)] => (Ok [body, t]) | _ => (Error "bad") end');
  });
});

/* ------------------------------------------------------------------ */
/*  if/then/else                                                       */
/* ------------------------------------------------------------------ */

describe('ML type checker: if/then/else', () => {
  it('accepts if/then/else returning Result', () => {
    ok('fun s => (if s then (Ok []) else (Error "bad") end)');
  });

  it('rejects if with mismatched branch types', () => {
    fails('fun s => (if s then (Ok []) else "wrong" end)');
  });
});

/* ------------------------------------------------------------------ */
/*  Nested structures                                                  */
/* ------------------------------------------------------------------ */

describe('ML type checker: nested structures', () => {
  it('match inside if', () => {
    ok('fun s => (if s then match s with | _ => (Ok []) end else (Error "bad") end)');
  });

  it('if inside match branch', () => {
    ok('fun s => match s with | _ => if s then (Ok []) else (Error "bad") end end');
  });

  it('nested match', () => {
    ok('fun s => match s with | [?first] => match first with | _ => (Ok []) end | _ => (Error "bad") end');
  });
});

/* ------------------------------------------------------------------ */
/*  The full schema definition example from ML.md                      */
/* ------------------------------------------------------------------ */

describe('ML type checker: full schema example', () => {
  it('type-checks the definition schema', () => {
    const code = [
      'fun s => match s with',
      '| [([(?x, ?t)], ?ret),',
      '   ([(?x_eq, eq ?t ?t ?body)], _)]',
      '    => (Ok [body, (refl t body)])',
      '| _ =>',
      '  if (List length s != two)',
      '  then (Error "definition declarations must have length 2")',
      '  else (Error "invalid declaration")',
      '  end',
      'end',
    ].join('\n');
    ok(code);
  });

  it('rejects schema that returns string', () => {
    fails('fun s => match s with | _ => "not a result" end');
  });

  it('rejects schema that forgets Error wrapper', () => {
    fails('fun s => match s with | _ => "message" end');
  });
});
