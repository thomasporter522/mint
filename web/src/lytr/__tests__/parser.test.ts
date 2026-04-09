import { describe, it, expect } from 'vitest';
// @ts-ignore
import { parseAndPrint, lexToTokens } from '@reason/Lytr_api.js';

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
  it('parses empty postulate block', () => {
    expect(pp('postulate\nend')).toBe('postulate  end');
  });

  it('parses postulate with one declaration', () => {
    expect(pp('postulate\nx : T\nend')).toBe('postulate x : T end');
  });

  it('parses postulate with multiple declarations', () => {
    expect(pp('postulate\nx : T\ny : S\nend')).toBe('postulate x : T\ny : S end');
  });

  it('parses postulate with function declaration', () => {
    // Parens around (f (a : T)) are preserved in the round-trip
    expect(pp('postulate\n(f (a : T)) : S\nend')).toBe('postulate (f (a : T)) : S end');
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

describe('lexer tokens', () => {
  it('produces correct token types', () => {
    const buf = lexToTokens('postulate x : (?) end') as number[];
    // Each token is [type, start, end]
    const tokens: [number, number, number][] = [];
    for (let i = 0; i < buf.length; i += 3) {
      tokens.push([buf[i], buf[i+1], buf[i+2]]);
    }

    // postulate=1, x=2, :=4, (=5, ?=3, )=6, end=1
    expect(tokens).toEqual([
      [1, 0, 9],   // "postulate" keyword
      [2, 10, 11],  // "x" identifier
      [4, 12, 13],  // ":" colon
      [5, 14, 15],  // "(" open paren
      [3, 15, 16],  // "?" hole
      [6, 16, 17],  // ")" close paren
      [1, 18, 21],  // "end" keyword
    ]);
  });

  it('classifies schema as keyword', () => {
    const buf = lexToTokens('schema') as number[];
    expect(buf[0]).toBe(1); // keyword
  });

  it('classifies construct as keyword', () => {
    const buf = lexToTokens('construct') as number[];
    expect(buf[0]).toBe(1); // keyword
  });

  it('classifies unknown chars as invalid', () => {
    const buf = lexToTokens('@') as number[];
    expect(buf[0]).toBe(7); // invalid
  });

  it('skips whitespace', () => {
    const buf = lexToTokens('  x  ') as number[];
    // Only one token: the identifier
    expect(buf.length).toBe(3);
    expect(buf[0]).toBe(2); // identifier
    expect(buf[1]).toBe(2); // start
    expect(buf[2]).toBe(3); // end
  });
});

/* ------------------------------------------------------------------ */
/*  Edge cases and error recovery                                      */
/* ------------------------------------------------------------------ */

describe('edge cases', () => {
  it('unmatched close paren becomes shard', () => {
    const result = pp(')');
    expect(result).toBe(')');
  });

  it('unmatched open paren becomes shard', () => {
    const result = pp('(');
    expect(result).toBe('(');
  });

  it('only whitespace produces empty output', () => {
    expect(pp('   ')).toBe('');
  });

  it('colon with nothing on either side', () => {
    // Should produce Asc(inserted_hole, inserted_hole)
    const result = pp(':');
    expect(result).toBe(' : ');
  });

  it('handles multiple colons', () => {
    // a : b : c — right-associative
    const result = pp('a : b : c');
    expect(result).toBe('a : b : c');
  });

  it('handles complex mixed expression', () => {
    const result = pp('f (a : T) (b : a) : b');
    expect(result).toBe('f (a : T) (b : a) : b');
  });

  it('postulate with application in type position', () => {
    expect(pp('postulate\nx : (f a)\nend')).toBe('postulate x : (f a) end');
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

describe('equals operator', () => {
  it('parses simple equals', () => {
    expect(pp('x = y')).toBe('x = y');
  });

  it('equals binds very loosely', () => {
    expect(pp('f : A -> B = body')).toBe('f : A -> B = body');
  });
});

describe('fat arrow', () => {
  it('parses fat arrow', () => {
    expect(pp('x => y')).toBe('x => y');
  });

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

  it('deeply nested pair with application', () => {
    expect(pp('[([(?x, f y)], z)]')).toBe('[([(?x, f y)], z)]');
  });
});

describe('pipe', () => {
  it('parses pipe', () => {
    expect(pp('a | b')).toBe('a | b');
  });

  it('pipe chains', () => {
    expect(pp('a | b | c')).toBe('a | b | c');
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

/* ------------------------------------------------------------------ */
/*  ML constructs: meta-variables                                      */
/* ------------------------------------------------------------------ */

describe('meta-variables', () => {
  it('parses ?x as identifier', () => {
    expect(pp('?x')).toBe('?x');
  });

  it('parses bare ? as hole', () => {
    expect(pp('?')).toBe('?');
  });

  it('meta-variable in application', () => {
    expect(pp('f ?x ?y')).toBe('f ?x ?y');
  });

  it('meta-variable in pattern-like context', () => {
    expect(pp('(?x, ?t)')).toBe('(?x, ?t)');
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

  it('wildcard parses', () => {
    expect(pp('_')).toBe('_');
  });
});

/* ------------------------------------------------------------------ */
/*  Full schema example                                                */
/* ------------------------------------------------------------------ */

describe('schema definition example', () => {
  it('parses the full schema definition from ML.md', () => {
    const code = [
      'schema definition : List Signature -> Result (List Term) =',
      '  fun s => match s with',
      '  | [([(?x, ?t)], ?ret),',
      '     ([(?x_eq, eq ?t ?t ?body)], _)]',
      '      => Ok [body, refl t body]',
      '  | _ =>',
      '    if List length s != two',
      '    then Error "definition declarations must have length 2"',
      '    else Error "invalid declaration"',
      '    end',
      '  end',
    ].join('\n');
    const result = pp(code);
    // Should not contain BUILDER ERROR
    expect(result).not.toContain('BUILDER ERROR');
    // Should preserve key structural elements
    expect(result).toContain('schema');
    expect(result).toContain('definition');
    expect(result).toContain('fun');
    expect(result).toContain('match');
    expect(result).toContain('Ok');
    expect(result).toContain('Error');
    expect(result).toContain('=>');
    expect(result).toContain('->');
    expect(result).toContain('"definition declarations must have length 2"');
    expect(result).toContain('"invalid declaration"');
  });
});
