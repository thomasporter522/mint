import { describe, it, expect } from 'vitest';
// @ts-ignore
import { parseAndPrint } from '../reason-bridge';

const pp = (code: string): string => parseAndPrint(code) as string;

/* ------------------------------------------------------------------ */
/*  Atoms                                                              */
/* ------------------------------------------------------------------ */

describe('atoms', () => {
  it('parses a single identifier', () => {
    expect(pp('x')).toBe('x');
  });

  it('parses a multi-char identifier', () => {
    expect(pp('foo')).toBe('foo');
  });

  it('parses identifier with digits and underscores', () => {
    expect(pp('x_1')).toBe('x_1');
  });

  it('parses identifier with hyphens', () => {
    expect(pp('my-var')).toBe('my-var');
  });

  it('parses a hole', () => {
    expect(pp('?')).toBe('?');
  });

  it('parses empty input as inserted hole', () => {
    expect(pp('')).toBe('');
  });
});

/* ------------------------------------------------------------------ */
/*  Application                                                        */
/* ------------------------------------------------------------------ */

describe('application', () => {
  it('parses binary application', () => {
    expect(pp('f x')).toBe('f x');
  });

  it('parses ternary application', () => {
    expect(pp('f x y')).toBe('f x y');
  });

  it('parses many arguments', () => {
    expect(pp('f a b c d')).toBe('f a b c d');
  });

  it('application is left-nested by default', () => {
    // f x y is Ap(f, [x, y]) which prints as "f x y"
    expect(pp('f x y')).toBe('f x y');
  });
});

/* ------------------------------------------------------------------ */
/*  Ascription (colon operator)                                        */
/* ------------------------------------------------------------------ */

describe('ascription', () => {
  it('parses simple ascription', () => {
    expect(pp('x : T')).toBe('x : T');
  });

  it('ascription binds looser than application', () => {
    // "f x : T" means (f x) : T
    expect(pp('f x : T')).toBe('f x : T');
  });

  it('right side of ascription can be application', () => {
    expect(pp('x : f y')).toBe('x : f y');
  });

  it('ascription is right-associative', () => {
    // "a : b : c" means a : (b : c)
    expect(pp('a : b : c')).toBe('a : b : c');
  });

  it('both sides can be complex', () => {
    expect(pp('f x y : g a b')).toBe('f x y : g a b');
  });
});

/* ------------------------------------------------------------------ */
/*  Parentheses                                                        */
/* ------------------------------------------------------------------ */

describe('parentheses', () => {
  it('wraps single identifier', () => {
    expect(pp('(x)')).toBe('(x)');
  });

  it('wraps application', () => {
    expect(pp('(f x)')).toBe('(f x)');
  });

  it('nested parens collapse', () => {
    // Inner parens set parens=true on x, outer parens do the same — no nesting
    expect(pp('((x))')).toBe('(x)');
  });

  it('parens override precedence', () => {
    // Without parens: f (x : T) means Ap(f, [Asc(x, T)])
    expect(pp('f (x : T)')).toBe('f (x : T)');
  });

  it('parens around ascription', () => {
    expect(pp('(x : T)')).toBe('(x : T)');
  });

  it('multiple parenthesized arguments', () => {
    expect(pp('f (a : T) (b : S)')).toBe('f (a : T) (b : S)');
  });

  it('empty parens produce inserted hole', () => {
    expect(pp('()')).toBe('()');
  });
});

/* ------------------------------------------------------------------ */
/*  Postulate blocks                                                   */
/* ------------------------------------------------------------------ */

describe('postulate blocks', () => {
  it('parses postulate with one declaration', () => {
    expect(pp('postulate\nx : T\nend')).toBe('postulate\nx : T\nend\n');
  });

  it('parses postulate with multiple declarations', () => {
    expect(pp('postulate\nx : T\ny : S\nend')).toBe('postulate\nx : T\ny : S\nend\n');
  });

  it('parses postulate with function declaration', () => {
    // The outer parens around the LHS (f (a : T)) are silly and the
    // printer drops them on round-trip.
    expect(pp('postulate\n(f (a : T)) : S\nend')).toBe('postulate\nf (a : T) : S\nend\n');
  });

  it('parses nested postulate blocks', () => {
    const result = pp('postulate\nx : T\npostulate\ny : S\nend\nend');
    expect(result).toContain('postulate');
    expect(result).toContain('end');
  });
});

/* ------------------------------------------------------------------ */
/*  Lexer token output                                                 */
/* ------------------------------------------------------------------ */

// Lexer-token tests removed — the OCaml `lexToTokens` API is gone. The
// new architecture uses Lezer's parser directly for highlighting.

/* ------------------------------------------------------------------ */
/*  Edge cases and error recovery                                      */
/* ------------------------------------------------------------------ */

describe('edge cases', () => {
  it('only whitespace produces empty output', () => {
    expect(pp('   ')).toBe('');
  });

  it('handles multiple colons', () => {
    // a : b : c — right-associative
    const result = pp('a : b : c');
    expect(result).toBe('a : b : c');
  });

  it('postulate with application in type position', () => {
    // Outer parens around the type expression are silly after `:` —
    // dropped on round-trip.
    expect(pp('postulate\nx : (f a)\nend')).toBe('postulate\nx : f a\nend\n');
  });

  it('preserves structure through round-trip', () => {
    const complex = 'postulate\n(arrow (A : Sort) (B : Sort)) : Sort\n(pi (A : Sort) (B : (arrow A Sort))) : Sort\nend';
    const result = pp(complex);
    expect(result).toContain('arrow');
    expect(result).toContain('pi');
    expect(result).toContain('Sort');
    expect(result).toContain('postulate');
    expect(result).toContain('end');
  });
});

/* ------------------------------------------------------------------ */
/*  ML constructs: infix operators                                     */
/* ------------------------------------------------------------------ */

describe('arrow operator', () => {
  it('parses simple arrow', () => {
    expect(pp('A -> B')).toBe('A -> B');
  });

  it('arrow is right-associative', () => {
    expect(pp('A -> B -> C')).toBe('A -> B -> C');
  });

  it('arrow binds tighter than colon', () => {
    // "x : A -> B" means x : (A -> B)
    expect(pp('x : A -> B')).toBe('x : A -> B');
  });
});

// `=` as a generic binary operator is gone — it only appears in meta-let
// and let-in bindings now (where it's a structural separator, not a binop).

describe('fat arrow', () => {
  it('fun with fat arrow', () => {
    expect(pp('fun x => x')).toBe('fun x => x');
  });
});

describe('tuples and commas', () => {
  it('parses pair', () => {
    expect(pp('(a, b)')).toBe('(a, b)');
  });

  it('parses triple', () => {
    expect(pp('(a, b, c)')).toBe('(a, b, c)');
  });

  it('application groups before comma', () => {
    // (a, f x) should be Comma(a, Ap(f, x)), not Ap(Comma(a, f), x)
    expect(pp('(a, f x)')).toBe('(a, f x)');
  });

  it('nested pairs', () => {
    expect(pp('((a, b), c)')).toBe('((a, b), c)');
  });

  it('pair inside list', () => {
    expect(pp('[(a, b), (c, d)]')).toBe('[(a, b), (c, d)]');
  });

  it('list inside pair', () => {
    expect(pp('([a, b], c)')).toBe('([a, b], c)');
  });

});

/* ------------------------------------------------------------------ */
/*  ML constructs: brackets                                            */
/* ------------------------------------------------------------------ */

describe('list literals', () => {
  it('parses empty list', () => {
    expect(pp('[]')).toBe('[]');
  });

  it('parses singleton list', () => {
    expect(pp('[x]')).toBe('[x]');
  });

  it('parses multi-element list', () => {
    expect(pp('[x, y, z]')).toBe('[x, y, z]');
  });

  it('parses nested list', () => {
    expect(pp('[[a, b], [c]]')).toBe('[[a, b], [c]]');
  });

  it('parses list of pairs', () => {
    // Inner parens protect commas from being collected into the outer list
    expect(pp('[(a, b), (c, d)]')).toBe('[(a, b), (c, d)]');
  });
});

/* ------------------------------------------------------------------ */
/*  ML constructs: string literals                                     */
/* ------------------------------------------------------------------ */

describe('string literals', () => {
  it('parses simple string', () => {
    expect(pp('"hello"')).toBe('"hello"');
  });

  it('parses string with spaces', () => {
    expect(pp('"hello world"')).toBe('"hello world"');
  });

  it('string in application', () => {
    expect(pp('Error "bad input"')).toBe('Error "bad input"');
  });
});

/* meta-variable (?x) syntax has been removed — pattern variables are
   plain identifiers now. The bare `?` hole is covered in the atoms
   describe block. */

describe('hole', () => {
  it('parses bare ? as hole', () => {
    expect(pp('?')).toBe('?');
  });
});

/* ------------------------------------------------------------------ */
/*  ML constructs: keywords                                            */
/* ------------------------------------------------------------------ */

describe('ML keywords', () => {
  it('fun keyword parses as identifier in application', () => {
    expect(pp('fun x => x')).toBe('fun x => x');
  });

  it('match/with parse', () => {
    const result = pp('match x with | y => z end');
    expect(result).toContain('match');
    expect(result).toContain('with');
    expect(result).toContain('x');
    expect(result).toContain('y');
    expect(result).toContain('end');
  });

  it('if/then/else parse', () => {
    const result = pp('if a then b else c end');
    expect(result).toContain('if');
    expect(result).toContain('then');
    expect(result).toContain('else');
    expect(result).toContain('a');
    expect(result).toContain('b');
    expect(result).toContain('c');
  });

  // `_` as a standalone expression isn't a thing — it appears in pattern
  // position, where it's covered by pattern tests in eval.test.ts.
});

/* ------------------------------------------------------------------ */
/*  Full schema example                                                */
/* ------------------------------------------------------------------ */

// Old ML.md schema example used `?x` meta-variables; that syntax is gone.
// Modern schema parsing is exercised by the example-file tests.
