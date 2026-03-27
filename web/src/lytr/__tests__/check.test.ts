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
    expect(errors('postulate\nx : Sort\nend')).toEqual([]);
  });

  it('accepts multiple declarations', () => {
    expect(errors('postulate\nx : Sort\ny : Sort\nend')).toEqual([]);
  });

  it('reports unbound variable', () => {
    const msgs = errorMessages('postulate\nx : y\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('earlier declaration is in scope for later ones', () => {
    expect(errors('postulate\nx : Sort\ny : x\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Function declarations and application                              */
/* ------------------------------------------------------------------ */

describe('function declarations', () => {
  it('accepts a function with one typed argument', () => {
    expect(errors('postulate\nx : Sort\n(f (a : Sort)) : Sort\nend')).toEqual([]);
  });

  it('accepts application with correct arity', () => {
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('reports too many arguments', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too many arguments'));
  });

  it('reports too few arguments', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too few arguments'));
  });
});

/* ------------------------------------------------------------------ */
/*  Argument scoping                                                   */
/* ------------------------------------------------------------------ */

describe('argument scoping', () => {
  it('argument bindings do not leak to the next line', () => {
    const msgs = errorMessages(
      'postulate\n(f (a : Sort)) : a\ng : a\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable a'));
  });

  it('argument is in scope for the return type of its own line', () => {
    expect(errors(
      'postulate\n(f (a : Sort)) : a\nend'
    )).toEqual([]);
  });

  it('multiple arguments are in scope for each other and return type', () => {
    expect(errors(
      'postulate\n(f (a : Sort) (b : a)) : b\nend'
    )).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Type consistency at application sites                               */
/* ------------------------------------------------------------------ */

describe('type consistency', () => {
  it('no error when expected type matches inferred', () => {
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('expected argument type is the TYPE, not the full ascription pattern', () => {
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort)) : a\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('rejects argument whose type does not match after substitution', () => {
    // pi expects (B : (arrow A Sort)). After A=Sort, second arg should be (arrow Sort Sort).
    // Bare Sort is not (arrow Sort Sort), so this should error.
    const msgs = errorMessages(
      'postulate\n(arrow (A : Sort) (B : Sort)) : Sort\n(pi (A : Sort) (B : (arrow A Sort))) : Sort\nx : (pi Sort Sort)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsitency'));
  });

  it('reports inconsistency for genuinely wrong types', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\ny : x\n(f (a : Sort)) : Sort\ng : (f y)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsitency'));
  });
});

/* ------------------------------------------------------------------ */
/*  Dependent return type substitution                                 */
/* ------------------------------------------------------------------ */

describe('return type substitution', () => {
  it('return type is substituted with the argument value (identity fn)', () => {
    // f : (a : Sort) -> a.  (f Sort) should have type Sort (= a[a:=Sort]).
    // g : (f Sort) should therefore be well-typed with g : Sort.
    // Then (f g) should also be fine: g has type Sort, return = a[a:=g] = g.
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort)) : a\ng : (f Sort)\na : (f g)\nend'
    )).toEqual([]);
  });

  it('return type substitution with non-dependent return type is harmless', () => {
    // f always returns Sort regardless of argument — substitution is a no-op.
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('second argument type is substituted with first argument value', () => {
    // f : (a : Sort) -> (b : a) -> b
    // x : Sort, y : x
    // (f x y): first arg x checked against Sort ✓, second arg y checked against a[a:=x] = x.
    //   y has type x ✓. Return type = b[a:=x, b:=y] = y.
    expect(errors(
      'postulate\nx : Sort\ny : x\n(f (a : Sort) (b : a)) : b\ng : (f x y)\nend'
    )).toEqual([]);
  });

  it('substitution detects type error in second argument', () => {
    // f : (a : Sort) -> (b : a) -> b
    // x : Sort, y : x
    // (f x x): second arg x checked against a[a:=x] = x. But x has type Sort, not x.
    const msgs = errorMessages(
      'postulate\nx : Sort\ny : x\n(f (a : Sort) (b : a)) : b\ng : (f x x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsitency'));
  });

  it('substitution chains through multiple arguments', () => {
    // f : (a : Sort) -> (b : a) -> (c : b) -> c
    // x : Sort, y : x, z : y
    // (f x y z): a:=x, then b's type = a[a:=x] = x, check y:x ✓,
    //   then c's type = b[a:=x,b:=y] = y, check z:y ✓,
    //   return = c[a:=x,b:=y,c:=z] = z
    expect(errors(
      'postulate\nx : Sort\ny : x\nz : y\n(f (a : Sort) (b : a) (c : b)) : c\ng : (f x y z)\nend'
    )).toEqual([]);
  });

  it('substitution in return type used for outer consistency check', () => {
    // f : (a : Sort) -> a.  x : Sort.
    // g expects type x, but (f Sort) returns a[a:=Sort] = Sort.
    // Sort and x are different, so this should error.
    const msgs = errorMessages(
      'postulate\nx : Sort\n(f (a : Sort)) : a\ng : x\nh : (f g)\nend'
    );
    // (f g): g has type x, checked against Sort — inconsistency
    expect(msgs).toContainEqual(expect.stringContaining('Inconsitency'));
  });

  it('non-dependent multi-arg function still works', () => {
    // No parameter names appear in the return type — substitution is vacuous.
    expect(errors(
      'postulate\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x x)\nend'
    )).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Holes                                                              */
/* ------------------------------------------------------------------ */

describe('holes', () => {
  it('does not loop on self-referential application in declaration RHS', () => {
    expect(() => errors(
      'postulate\n(eq (A : Sort) (B : Sort) (a : A) (b : B)) : Sort\n(refl (A : Sort) (a : A)) : (eq A ? ? ?)\nend'
    )).not.toThrow();
  });

  it('hole gets the expected type as its goal', () => {
    const g = goalString('postulate\nx : Sort\ng : ?\nend');
    expect(g).toBe('?');
  });

  it('hole in application position gets the argument type as goal', () => {
    const h = holes('postulate\nx : Sort\n(f (a : Sort)) : Sort\ng : (f ?)\nend');
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    expect(goal).toBe('Sort');
  });

  it('hole in second arg position gets substituted type as goal', () => {
    // f : (a : Sort) -> (b : a) -> b.  (f x ?): second arg expects a[a:=x] = x.
    const h = holes(
      'postulate\nx : Sort\n(f (a : Sort) (b : a)) : b\ng : (f x ?)\nend'
    );
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    expect(goal).toBe('x');
  });
});
