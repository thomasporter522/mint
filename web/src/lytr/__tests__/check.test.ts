import { describe, it, expect } from 'vitest';
// @ts-ignore
import { processCode, printTerm } from '@reason/Lytr_api.js';

/* ------------------------------------------------------------------ */
/*  Helpers                                                            */
/* ------------------------------------------------------------------ */

type Error = { type: string; message: string; from: number; to: number };
type HoleInfo = { goal: any; context: any };
type Result = { errors: Error[]; holes: [number, HoleInfo][] };

function check(code: string): Result {
  return processCode(code) as Result;
}

function errors(code: string): Error[] {
  return check(code).errors;
}

function errorMessages(code: string): string[] {
  return errors(code).map(e => e.message);
}

function holes(code: string): [number, HoleInfo][] {
  return check(code).holes;
}

function goalString(code: string, index = 0): string {
  const h = holes(code);
  expect(h.length).toBeGreaterThan(index);
  return printTerm(h[index][1].goal);
}

/* ------------------------------------------------------------------ */
/*  Basic well-formedness                                              */
/* ------------------------------------------------------------------ */

describe('basic postulate blocks', () => {
  it('accepts a simple declaration', () => {
    expect(errors('postulate\nx : U\nend')).toEqual([]);
  });

  it('accepts multiple declarations', () => {
    expect(errors('postulate\nx : U\ny : U\nend')).toEqual([]);
  });

  it('reports unbound variable', () => {
    const msgs = errorMessages('postulate\nx : y\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('earlier declaration is in scope for later ones', () => {
    expect(errors('postulate\nx : U\ny : x\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Function declarations and application                              */
/* ------------------------------------------------------------------ */

describe('function declarations', () => {
  it('accepts a function with one typed argument', () => {
    expect(errors('postulate\nx : U\n(f (a : U)) : U\nend')).toEqual([]);
  });

  it('accepts application with correct arity', () => {
    expect(errors(
      'postulate\nx : U\n(f (a : U)) : U\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('reports too many arguments', () => {
    const msgs = errorMessages(
      'postulate\nx : U\n(f (a : U)) : U\ng : (f x x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too many arguments'));
  });

  it('reports too few arguments', () => {
    const msgs = errorMessages(
      'postulate\nx : U\n(f (a : U) (b : U)) : U\ng : (f x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too few arguments'));
  });
});

/* ------------------------------------------------------------------ */
/*  Argument scoping                                                   */
/* ------------------------------------------------------------------ */

describe('argument scoping', () => {
  it('argument bindings do not leak to the next line', () => {
    // 'a' is bound only inside the line defining f; it should not
    // be visible when checking g.
    const msgs = errorMessages(
      'postulate\n(f (a : U)) : a\ng : a\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable a'));
  });

  it('argument is in scope for the return type of its own line', () => {
    expect(errors(
      'postulate\n(f (a : U)) : a\nend'
    )).toEqual([]);
  });

  it('multiple arguments are in scope for each other and return type', () => {
    expect(errors(
      'postulate\n(f (a : U) (b : a)) : b\nend'
    )).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Type consistency at application sites                               */
/* ------------------------------------------------------------------ */

describe('type consistency', () => {
  it('no error when expected type matches inferred', () => {
    // f : U -> U,  x : U  =>  (f x) should have type U
    expect(errors(
      'postulate\nx : U\n(f (a : U)) : U\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('expected argument type is the TYPE, not the full ascription pattern', () => {
    // f expects an argument of type U (from (a : U)).
    // x : U, so (f x) should be fine and the return type is 'a'
    // which was bound to x's type.  No "Inconsistency" error should appear.
    expect(errors(
      'postulate\nx : U\n(f (a : U)) : a\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('reports inconsistency for genuinely wrong types', () => {
    // f returns U, but g expects something that should be x (which is declared as U).
    // Actually let's make a clear mismatch:
    // x : U, y : x, f : U -> x, g : y = (f y) — f expects U but gets y:x
    const msgs = errorMessages(
      'postulate\nx : U\ny : x\n(f (a : U)) : U\ng : (f y)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsitency'));
  });
});

/* ------------------------------------------------------------------ */
/*  Holes                                                              */
/* ------------------------------------------------------------------ */

describe('holes', () => {
  it('hole gets the expected type as its goal', () => {
    const g = goalString('postulate\nx : U\ng : ?\nend');
    expect(g).toBe('?');  // hole with no specific expected type
  });

  it('hole in application position gets the argument type as goal', () => {
    const h = holes('postulate\nx : U\n(f (a : U)) : U\ng : (f ?)\nend');
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    expect(goal).toBe('U');
  });
});
