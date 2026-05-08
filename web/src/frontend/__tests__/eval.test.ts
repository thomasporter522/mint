import { describe, it, expect } from 'vitest';
// @ts-ignore
import { evalCode, parseAndPrint } from '../reason-bridge';

type EvalResult = { ok: boolean; value: string; error: string };

const eval_ = (code: string): EvalResult => evalCode(code) as EvalResult;

const evalOk = (code: string): string => {
  const r = eval_(code);
  if (!r.ok) throw new Error(`Expected Ok, got Err: ${r.error}\nCode: ${code}`);
  return r.value;
};

const evalErr = (code: string): string => {
  const r = eval_(code);
  if (r.ok) throw new Error(`Expected Err, got Ok: ${r.value}\nCode: ${code}`);
  return r.error;
};

/* ------------------------------------------------------------------ */
/*  Atoms and literals                                                  */
/* ------------------------------------------------------------------ */

describe('eval: atoms', () => {
  it('identifier passes through as OL term', () => {
    expect(evalOk('x')).toBe('x');
  });

  it('string literal evaluates to itself', () => {
    expect(evalOk('"hello"')).toBe('"hello"');
  });

  it('hole evaluates to itself', () => {
    expect(evalOk('?')).toBe('?');
  });
});

/* ------------------------------------------------------------------ */
/*  Lists                                                               */
/* ------------------------------------------------------------------ */

describe('eval: lists', () => {
  it('empty list', () => {
    expect(evalOk('[]')).toBe('[]');
  });

  it('list of identifiers', () => {
    expect(evalOk('[x, y, z]')).toBe('[x, y, z]');
  });

  it('nested list', () => {
    expect(evalOk('[[a], [b, c]]')).toBe('[[a], [b, c]]');
  });
});

/* ------------------------------------------------------------------ */
/*  Cons (:: operator)                                                  */
/* ------------------------------------------------------------------ */

describe('eval: cons', () => {
  it('cons with literal tail', () => {
    expect(evalOk('a :: [b, c]')).toBe('[a, b, c]');
  });

  it('cons with empty tail', () => {
    expect(evalOk('a :: []')).toBe('[a]');
  });

  it('cons onto singleton', () => {
    expect(evalOk('a :: [b]')).toBe('[a, b]');
  });

  it('cons pattern matches head and tail', () => {
    expect(evalOk('match [a, b, c] with | h :: t => t end')).toBe('[b, c]');
  });

  it('cons pattern with nested cons', () => {
    expect(evalOk('match [a, b, c] with | x :: y :: t => (x, y) end')).toBe('(a, b)');
  });

  it('cons pattern fails on too-short list', () => {
    expect(evalOk('match [a] with | x :: y :: t => no | _ => yes end')).toBe('yes');
  });

  it('cons pattern with empty tail', () => {
    expect(evalOk('match [a] with | h :: t => t end')).toBe('[]');
  });

  it('cons round-trips through pattern and expression', () => {
    expect(evalOk('match [x, y, z] with | h :: t => h :: t end')).toBe('[x, y, z]');
  });

  it('reverse via foldl and cons', () => {
    expect(evalOk('foldl (fun acc => fun x => x :: acc) [] [a, b, c]')).toBe('[c, b, a]');
  });

  it('prepend all via foldl and cons', () => {
    // foldl prepends each element, so [a,b] folded onto [c,d] gives [d,c,a,b]
    expect(evalOk(
      'foldl (fun acc => fun x => x :: acc) [a, b] [c, d]'
    )).toBe('[d, c, a, b]');
  });
});

/* ------------------------------------------------------------------ */
/*  Pairs                                                               */
/* ------------------------------------------------------------------ */

describe('eval: pairs', () => {
  it('pair of identifiers', () => {
    expect(evalOk('(a, b)')).toBe('(a, b)');
  });

  it('nested pair', () => {
    expect(evalOk('(a, (b, c))')).toBe('(a, (b, c))');
  });

  it('list of pairs', () => {
    expect(evalOk('[(a, b), (c, d)]')).toBe('[(a, b), (c, d)]');
  });
});

/* ------------------------------------------------------------------ */
/*  Function application                                                */
/* ------------------------------------------------------------------ */

describe('eval: function application', () => {
  it('identity function', () => {
    expect(evalOk('(fun x => x) a')).toBe('a');
  });

  it('constant function', () => {
    expect(evalOk('(fun x => y) a')).toBe('y');
  });

  it('function returning a list', () => {
    expect(evalOk('(fun x => [x, x]) a')).toBe('[a, a]');
  });

  it('function returning a pair', () => {
    expect(evalOk('(fun x => (x, x)) a')).toBe('(a, a)');
  });

  it('nested function application (currying)', () => {
    expect(evalOk('(fun x => fun y => (x, y)) a b')).toBe('(a, b)');
  });

  it('closure captures environment', () => {
    expect(evalOk('(fun x => fun y => x) a b')).toBe('a');
  });

  it('OL term application passes through', () => {
    expect(evalOk('(f a b)')).toBe('f a b');
  });

  it('Ok constructor', () => {
    expect(evalOk('(Ok [a, b])')).toBe('Ok [a, b]');
  });

  it('Error constructor', () => {
    expect(evalOk('(Error "bad")')).toBe('Error "bad"');
  });
});

/* ------------------------------------------------------------------ */
/*  Pattern matching                                                    */
/* ------------------------------------------------------------------ */

describe('eval: pattern matching', () => {
  it('wildcard pattern matches anything', () => {
    expect(evalOk('match x with | _ => y end')).toBe('y');
  });

  it('variable pattern binds value', () => {
    expect(evalOk('match a with | x => x end')).toBe('a');
  });

  it('list pattern matches list', () => {
    expect(evalOk('match [a, b] with | [x, y] => (x, y) end')).toBe('(a, b)');
  });

  it('empty list pattern matches empty list', () => {
    expect(evalOk('match [] with | [] => yes | _ => no end')).toBe('yes');
  });

  it('list pattern fails on wrong length', () => {
    expect(evalOk('match [a] with | [x, y] => no | _ => yes end')).toBe('yes');
  });

  it('pair pattern matches pair', () => {
    expect(evalOk('match (a, b) with | (x, y) => [x, y] end')).toBe('[a, b]');
  });

  it('nested pattern matching', () => {
    expect(evalOk('match [(a, b)] with | [(x, y)] => (y, x) end')).toBe('(b, a)');
  });

  it('application pattern matches OL terms', () => {
    expect(evalOk('match (f a b) with | (g x y) => [g, x, y] end')).toBe('[f, a, b]');
  });

  it('string pattern matches string', () => {
    expect(evalOk('match "hi" with | "hi" => yes | _ => no end')).toBe('yes');
  });

  it('string pattern fails on different string', () => {
    expect(evalOk('match "hi" with | "bye" => no | _ => yes end')).toBe('yes');
  });

  it('first matching branch wins', () => {
    expect(evalOk('match a with | x => first | y => second end')).toBe('first');
  });

  it('falls through to second branch', () => {
    expect(evalOk('match [a, b] with | [] => no | [x, y] => yes end')).toBe('yes');
  });

  it('non-exhaustive match produces error', () => {
    expect(evalErr('match [a, b] with | [] => no end')).toContain('Non-exhaustive');
  });

  it('repeated variable in pattern is equality constraint', () => {
    expect(evalOk('match (a, a) with | (x, x) => yes | _ => no end')).toBe('yes');
  });

  it('repeated variable fails when values differ', () => {
    expect(evalOk('match (a, b) with | (x, x) => no | _ => yes end')).toBe('yes');
  });

  it('nonlinear pattern in Ap: eq x x matches eq a a', () => {
    expect(evalOk('match (eq a a) with | (eq x x) => yes | _ => no end')).toBe('yes');
  });

  it('nonlinear pattern in Ap: eq x x rejects eq a b', () => {
    expect(evalOk('match (eq a b) with | (eq x x) => yes | _ => no end')).toBe('no');
  });

  it('nonlinear across list elements: x bound in first, constrained in second', () => {
    expect(evalOk('match [(a, x), (b, x)] with | [(_, v), (_, v)] => yes | _ => no end')).toBe('yes');
  });

  it('nonlinear across list elements: constraint fails when values differ', () => {
    expect(evalOk('match [(a, x), (b, y)] with | [(_, v), (_, v)] => yes | _ => no end')).toBe('no');
  });

  it('nonlinear in nested Ap: eq ret ret f body with consistent ret', () => {
    expect(evalOk('match (eq D D I K) with | (eq r r f body) => (Ok r) | _ => no end')).toBe('Ok D');
  });

  it('nonlinear in nested Ap: eq ret ret f body with inconsistent ret', () => {
    expect(evalOk('match (eq D U I K) with | (eq r r f body) => (Ok r) | _ => no end')).toBe('no');
  });

  it('hole in pattern is wildcard', () => {
    expect(evalOk('match (a, b) with | (?, y) => y end')).toBe('b');
  });
});

/* ------------------------------------------------------------------ */
/*  If/then/else                                                        */
/* ------------------------------------------------------------------ */

describe('eval: if/then/else', () => {
  it('true branch', () => {
    expect(evalOk('(if true then a else b end)')).toBe('a');
  });

  it('false branch', () => {
    expect(evalOk('(if false then a else b end)')).toBe('b');
  });

  it('condition from equality', () => {
    expect(evalOk('(if a == a then yes else no end)')).toBe('yes');
  });

  it('inequality', () => {
    expect(evalOk('(if a != b then yes else no end)')).toBe('yes');
  });
});

/* ------------------------------------------------------------------ */
/*  Binary operators                                                    */
/* ------------------------------------------------------------------ */

describe('eval: binary operators', () => {
  it('== on equal terms', () => {
    expect(evalOk('a == a')).toBe('true');
  });

  it('== on different terms', () => {
    expect(evalOk('a == b')).toBe('false');
  });

  it('!= on different terms', () => {
    expect(evalOk('a != b')).toBe('true');
  });

  it('&& true true', () => {
    expect(evalOk('true && true')).toBe('true');
  });

  it('&& true false', () => {
    expect(evalOk('true && false')).toBe('false');
  });

  it('|| false true', () => {
    expect(evalOk('false || true')).toBe('true');
  });

  it('|| false false', () => {
    expect(evalOk('false || false')).toBe('false');
  });

  it('== on complex terms', () => {
    expect(evalOk('(f a b) == (f a b)')).toBe('true');
  });

  it('== on structurally different terms', () => {
    expect(evalOk('(f a) == (f b)')).toBe('false');
  });
});

/* ------------------------------------------------------------------ */
/*  Schema-like evaluation (the real use case)                          */
/* ------------------------------------------------------------------ */

describe('eval: schema execution', () => {
  it('definition schema applied to matching input', () => {
    // The definition schema:
    //   fun s => match s with
    //   | [(f, [], ret), (f_eq, [], eq ret ret f body)] => Ok [body, (refl ret body)]
    //   | _ => Error "invalid"
    //
    // Applied to signatures for:
    //   I : D
    //   I-eq : (eq D D I (ap (ap S K) K))
    //
    // Signature list: [("I", [], D), ("I-eq", [], (eq D D I (ap (ap S K) K)))]
    const schema = [
      'fun s => match s with',
      '| [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '    => (Ok [body, (refl ret body)])',
      '| _ => (Error "invalid")',
      'end',
    ].join(' ');

    const sigs = '[(I, [], D), (I-eq, [], (eq D D I (ap (ap S K) K)))]';
    const code = `(${schema}) ${sigs}`;
    const result = evalOk(code);
    expect(result).toContain('Ok');
    expect(result).toContain('ap');
    expect(result).toContain('refl');
  });

  it('definition schema rejects wrong number of declarations', () => {
    const schema = [
      'fun s => match s with',
      '| [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '    => (Ok [body, (refl ret body)])',
      '| _ => (Error "invalid")',
      'end',
    ].join(' ');

    const sigs = '[(I, [], D)]';
    const code = `(${schema}) ${sigs}`;
    const result = evalOk(code);
    expect(result).toContain('Error');
    expect(result).toContain('invalid');
  });

  it('definition schema rejects non-equation second declaration', () => {
    const schema = [
      'fun s => match s with',
      '| [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '    => (Ok [body, (refl ret body)])',
      '| _ => (Error "invalid")',
      'end',
    ].join(' ');

    const sigs = '[(I, [], D), (J, [], D)]';
    const code = `(${schema}) ${sigs}`;
    const result = evalOk(code);
    expect(result).toContain('Error');
  });

  it('always-error schema returns Error', () => {
    const code = '(fun s => (Error "nope")) [x]';
    const result = evalOk(code);
    expect(result).toContain('Error');
    expect(result).toContain('nope');
  });
});
