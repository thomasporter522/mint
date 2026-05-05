import { describe, it, expect } from 'vitest';
// @ts-ignore
import { checkSchemaCode } from '../reason-bridge';

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

  it('accepts match with tuple patterns in list', () => {
    ok('fun s => match s with | [(name, params, ret)] => (Ok []) | _ => (Error "bad") end');
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
    ok('fun s => match s with | [(name, [(x, t)], ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });

  it('binds meta-variables for use in body', () => {
    ok('fun s => match s with | [(name, [(x, t)], ret)] => (Ok [t]) | _ => (Error "bad") end');
  });

  it('binds meta-variables from OL application patterns', () => {
    ok('fun s => match s with | [(name, [(x, eq t body)], _)] => (Ok [body, t]) | _ => (Error "bad") end');
  });
});

/* ------------------------------------------------------------------ */
/*  if/then/else                                                       */
/* ------------------------------------------------------------------ */

describe('ML type checker: if/then/else', () => {
  it('accepts if/then/else returning Result', () => {
    ok('fun s => (if s == s then (Ok []) else (Error "bad") end)');
  });

  it('rejects if with mismatched branch types', () => {
    fails('fun s => (if s == s then (Ok []) else "wrong" end)');
  });
});

/* ------------------------------------------------------------------ */
/*  Nested structures                                                  */
/* ------------------------------------------------------------------ */

describe('ML type checker: nested structures', () => {
  it('match inside if', () => {
    ok('fun s => (if s == s then match s with | _ => (Ok []) end else (Error "bad") end)');
  });

  it('if inside match branch', () => {
    ok('fun s => match s with | _ => if s == s then (Ok []) else (Error "bad") end end');
  });

  it('nested match', () => {
    ok('fun s => match s with | [first] => match first with | _ => (Ok []) end | _ => (Error "bad") end');
  });
});

/* ------------------------------------------------------------------ */
/*  The full schema definition example from ML.md                      */
/* ------------------------------------------------------------------ */

describe('ML type checker: full schema example', () => {
  it('type-checks the definition schema', () => {
    const code = [
      'fun s => match s with',
      '| [(f, params, ret),',
      '   (f_eq, eq_params, eq ret ret (f params) body)]',
      '    => (Ok [body, (refl ret body)])',
      '| _ =>',
      '  (Error "invalid definition")',
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

/* ------------------------------------------------------------------ */
/*  x binding behavior                                                */
/* ------------------------------------------------------------------ */

describe('ML type checker: x binding', () => {
  it('x in pattern is usable as x in body', () => {
    ok('fun s => match s with | [(name, params, ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });

  it('bare x (no ?) in body does NOT reference x binding', () => {
    // In standalone mode (olNames=None), bare identifiers are permissive
    // So this passes — but ret resolves as an OL term, not the pattern-bound ret
    ok('fun s => match s with | [(name, params, ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });

  it('repeated x in pattern acts as equality constraint', () => {
    ok('fun s => match s with | [(n, p, ret), (n2, p2, eq ret ret f body)] => (Ok [body]) | _ => (Error "bad") end');
  });

  it('bare ? is a wildcard, not a named binding', () => {
    ok('fun s => match s with | [?] => (Ok []) | _ => (Error "bad") end');
  });

  it('name component has type Term', () => {
    // name binds at Term (first component of signature triple — the OL identifier)
    ok('fun s => match s with | [(name, params, ret)] => (Ok [name]) | _ => (Error "bad") end');
  });

  it('params component has type List (String, Term), not List Term', () => {
    // params : List (String, Term), so Ok params fails (Ok wants List Term)
    fails('fun s => match s with | [(name, params, ret)] => (Ok params) | _ => (Error "bad") end', 'Expected List Term');
    // And using params where String is expected also fails
    fails('fun s => match s with | [(name, params, ret)] => (Error params) | _ => (Error "bad") end', 'Expected String');
  });
});

/* ------------------------------------------------------------------ */
/*  Signature type (3-tuple)                                           */
/* ------------------------------------------------------------------ */

describe('ML type checker: signature type', () => {
  it('3-tuple pattern matches signature', () => {
    ok('fun s => match s with | [(name, params, ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });

  it('old 2-tuple pattern fails on signature', () => {
    // 2-tuple pattern against 3-tuple signature — arity mismatch
    fails('fun s => match s with | [(params, ret)] => (Ok [ret]) | _ => (Error "bad") end', 'Tuple pattern');
  });

  it('nested param destructuring works', () => {
    ok('fun s => match s with | [(name, [(pname, pty)], ret)] => (Ok [pty]) | _ => (Error "bad") end');
  });

  it('empty params list pattern works', () => {
    ok('fun s => match s with | [(name, [], ret)] => (Ok [ret]) | _ => (Error "bad") end');
  });
});

/* ------------------------------------------------------------------ */
/*  MTerm must not act as wildcard — type mismatches must be caught    */
/* ------------------------------------------------------------------ */

describe('ML type checker: Term is not a wildcard', () => {
  it('string where Term expected is rejected', () => {
    fails('fun s => (Ok ["hello"])', 'Expected Term');
  });

  it('list where Term expected is rejected', () => {
    // Ok wants List Term; if an element is a list, that's List Term not Term
    fails('fun s => (Ok [[x, y]])', 'Expected Term');
  });

  it('pair where Term expected is rejected', () => {
    fails('fun s => match s with | [(name, params, ret)] => (Ok [(name, ret)]) | _ => (Error "bad") end', 'Expected Term');
  });

  it('bool where Term expected is rejected', () => {
    fails('fun s => (Ok [x == y])', 'Expected Term');
  });

  it('Term where String expected is rejected', () => {
    fails('fun s => (Error x)', 'Expected String');
  });

  it('Term where Bool expected is rejected', () => {
    fails('fun s => (if x then (Ok []) else (Error "bad") end)');
  });

  it('Term where List expected is rejected', () => {
    fails('fun s => match s with | [(n, p, r)] => (Ok r) | _ => (Error "bad") end', 'Expected List');
  });

  it('fst on pair returns the left type, not Term', () => {
    // fst (name, params) returns Term (name's type), not a wildcard
    // Using it as a list element in Ok is fine since name : Term
    ok('fun s => match s with | [(name, params, ret)] => (Ok [fst (name, ret)]) | _ => (Error "bad") end');
  });

  it('snd on pair returns the right type, not Term', () => {
    ok('fun s => match s with | [(name, params, ret)] => (Ok [snd (name, ret)]) | _ => (Error "bad") end');
  });

  it('fst of pair with list left returns List, not Term', () => {
    // fst (params, name) where params : List (Term, Term) returns List (Term, Term)
    // Using that as a Term element in Ok should fail
    fails('fun s => match s with | [(name, params, ret)] => (Ok [fst (params, name)]) | _ => (Error "bad") end', 'Expected Term');
  });

  it('let binding preserves inferred type', () => {
    // let x = [a, b] makes x : List Term, using x where Term expected fails
    fails('fun s => let x = [a, b] in (Ok [x])', 'Expected Term');
  });

  it('let binding of pair is typed as pair', () => {
    fails('fun s => let x = (a, b) in (Ok [x])', 'Expected Term');
  });

  it('let binding of string is typed as string', () => {
    fails('fun s => let x = "hi" in (Ok [x])', 'Expected Term');
  });

  it('match branch types must agree', () => {
    // First branch returns Result (List Term), second must too
    fails('fun s => match s with | [] => (Ok []) | _ => [] end');
  });

  it('if branches must have same type', () => {
    fails('fun s => (if true then (Ok []) else [] end)');
  });
});

/* ------------------------------------------------------------------ */
/*  Type annotations on let bindings                                   */
/* ------------------------------------------------------------------ */

describe('ML type checker: let type annotations', () => {
  /* --- Annotations that should pass --- */

  it('annotated let with Term type', () => {
    ok('fun s => let x : Term = a in (Ok [x])');
  });

  it('annotated let with List Term type', () => {
    ok('fun s => let xs : (List Term) = [a, b] in (Ok xs)');
  });

  it('annotated let with String type', () => {
    ok('fun s => let msg : String = "hi" in (Error msg)');
  });

  it('annotated let with arrow type', () => {
    ok('fun s => let f : (Term -> Term) = fun x => x in (Ok [(f a)])');
  });

  it('annotated let with pair type', () => {
    ok('fun s => let p : (Term, Term) = (a, b) in (Ok [fst p])');
  });

  it('annotated let body is checked against the annotation', () => {
    // fun x => x is checked against Term -> Term, binding x as Term
    ok('fun s => let f : (Term -> Term) = fun x => x in (Ok [(f a)])');
  });

  it('annotated let with List Term -> List Term', () => {
    ok('fun s => let rev : ((List Term) -> (List Term)) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs) in (Ok (rev [a, b]))');
  });

  it('annotation gives param types to lambda', () => {
    // Without annotation, f infers as Term -> Term (param is Term).
    // With annotation (List Term) -> (List Term), param xs gets List Term.
    // Then foldl can properly type-check the callback.
    ok('fun s => let rev : ((List Term) -> (List Term)) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs) in (Ok (rev [a]))');
  });

  it('annotated let with Result type', () => {
    ok('fun s => let r : (Result (List Term)) = (Ok [a]) in r');
  });

  it('annotation propagates through function application', () => {
    // rev has type (List Term) -> (List Term), so (rev xs) returns List Term
    // Then (Ok (rev xs)) should pass since Ok wants List Term
    ok('fun s => let rev : ((List Term) -> (List Term)) = fun xs => (foldl (fun acc => fun x => x :: acc) [] xs) in match s with | _ => (Ok (rev [a, b])) end');
  });

  /* --- Annotations that should fail --- */

  it('rejects body that does not match annotation', () => {
    fails('fun s => let x : String = [a, b] in (Error x)', 'Expected String');
  });

  it('rejects using annotated binding at wrong type', () => {
    // x : String, but Ok wants List Term
    fails('fun s => let x : String = "hi" in (Ok [x])', 'Expected Term');
  });

  it('rejects arrow annotation on non-function', () => {
    fails('fun s => let f : (Term -> Term) = a in (Ok [(f a)])', 'Expected Term -> Term');
  });

  it('rejects List annotation on non-list body', () => {
    fails('fun s => let xs : (List Term) = a in (Ok xs)', 'Expected List');
  });

  it('rejects pair annotation on non-pair body', () => {
    fails('fun s => let p : (Term, Term) = a in (Ok [fst p])', 'Expected (Term, Term)');
  });

  it('annotation mismatch is caught even when body type-checks in isolation', () => {
    // Body [a, b] is valid as List Term, but annotation says String
    fails('fun s => let xs : String = [a, b] in (Error xs)', 'Expected String');
  });
});
