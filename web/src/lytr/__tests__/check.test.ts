import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
// @ts-ignore
import { processCode, printTerm, parseAndPrint } from '@reason/Lytr_api.js';

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

/* ------------------------------------------------------------------ */
/*  Schema blocks — ML type errors through unified pipeline            */
/* ------------------------------------------------------------------ */

describe('schema blocks', () => {
  it('accepts a valid schema in a block chain', () => {
    const code = [
      'postulate',
      'x : Sort',
      'schema',
      'foo = fun s => match s with | _ => (Ok []) end',
      'construct by foo',
      'y : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('reports ML type error in schema body', () => {
    const code = [
      'postulate',
      'x : Sort',
      'schema',
      'foo = fun s => match s with | _ => "wrong" end',
      'construct by foo',
      'y : x',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.length).toBeGreaterThan(0);
  });

  it('reports error when schema body returns wrong type', () => {
    const code = [
      'postulate',
      'x : Sort',
      'schema',
      'foo = fun s => match s with | _ => x end',
      'construct by foo',
      'y : x',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.length).toBeGreaterThan(0);
  });

  it('accepts schema with Ok wrapping terms', () => {
    const code = [
      'postulate',
      'x : Sort',
      'schema',
      'foo = fun s => match s with | [(name, [(a, t)], ret)] => (Ok [t]) | _ => (Error "bad") end',
      'construct by foo',
      'y : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('reports error for bare identifier in schema (no = body)', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\nschema\nx\nend'
    );
    expect(msgs.length).toBeGreaterThan(0);
  });

  it('reports type annotation mismatch', () => {
    const msgs = errorMessages(
      'schema\ndeclaration : Bool = ?\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Schema type mismatch'));
  });

  it('accepts correct type annotation with parens', () => {
    const code = [
      'postulate',
      'x : Sort',
      'schema',
      'foo : ((List Signature) -> (Result (List Term))) = fun s => match s with | _ => (Ok []) end',
      'construct by foo',
      'y : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('accepts correct type annotation written out fully', () => {
    expect(errors(
      'schema\ndeclaration : ((List (String, (List (String, Term)), Term)) -> (Result (List Term))) = ?\nend'
    )).toEqual([]);
  });

  it('unknown identifier in OL pattern binds as pattern variable', () => {
    // Without ? convention, unknown identifiers in OL patterns are binders
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      'schema',
      'foo = fun s => match s with',
      '  | [(f, [], eq2 ret ret f body)] => (Ok [body])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    // eq2 is not in scope but binds as a pattern variable — no error
    expect(errors(code)).toEqual([]);
  });

  it('schema errors do not leak into surrounding blocks', () => {
    const code = 'postulate\nU : Sort\nschema\ndeclaration = fun x => ?\nend';
    const errs = errors(code);
    // Should have schema body errors but NOT postulate errors
    const unboundU = errs.filter((e: Error) => e.message.includes('Unbound variable U'));
    expect(unboundU).toEqual([]);
    // The postulate block should be fine
    const unexpectedToken = errs.filter((e: Error) => e.message === 'Unexpected token');
    expect(unexpectedToken).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Construct blocks — OL declaration checking                         */
/* ------------------------------------------------------------------ */

describe('construct blocks', () => {
  it('checks construct by declarations like postulate', () => {
    expect(errors(
      'postulate\nx : Sort\nconstruct by foo\ny : x\nend'
    )).toEqual([]);
  });

  it('reports unbound variable in construct declaration', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\nconstruct by foo\ny : z\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('postulate context flows into construct declarations', () => {
    expect(errors(
      'postulate\nx : Sort\ny : x\nconstruct by foo\nz : y\nend'
    )).toEqual([]);
  });

  it('full chain: postulate context flows through schema to construct', () => {
    const code = [
      'postulate',
      'x : Sort',
      'y : x',
      'schema',
      'foo = fun s => match s with | _ => (Ok []) end',
      'construct by foo',
      'z : y',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('construct declarations extend the context', () => {
    const code = [
      'postulate',
      'x : Sort',
      'construct by foo',
      'y : x',
      'z : y',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('full definition schema example passes with no errors', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      '(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
      '(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))',
      'schema',
      'definition =',
      '  fun s => match s with',
      '  | [(f, [], ret),',
      '     (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid definition")',
      '  end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Shard and BuilderError reporting                                   */
/* ------------------------------------------------------------------ */

describe('shard and syntax errors', () => {
  it('reports shard errors with positions', () => {
    const errs = errors('postulate\nx : Sort\nend\n)');
    const positioned = errs.filter((e: Error) => e.from >= 0);
    expect(positioned.length).toBeGreaterThan(0);
  });

  it('shard at position 0 has from=0', () => {
    const errs = errors(')');
    expect(errs.length).toBeGreaterThan(0);
    expect(errs[0].from).toBe(0);
  });

  it('multiple shards get distinct positions', () => {
    const errs = errors(') )');
    const shardErrs = errs.filter(e => e.message === 'Unexpected token');
    expect(shardErrs.length).toBe(2);
    expect(shardErrs[0].from).not.toBe(shardErrs[1].from);
  });

  it('empty file does not crash', () => {
    expect(() => errors('')).not.toThrow();
  });

  it('shard inside construct block does not crash', () => {
    // Shards inside block bodies are filtered by buildItems (known limitation)
    expect(() => errors('postulate\nx : Sort\nconstruct by foo\n)\nend')).not.toThrow();
  });
});

/* ------------------------------------------------------------------ */
/*  OL scope checking in schemas                                       */
/* ------------------------------------------------------------------ */

describe('OL scope checking in schemas', () => {
  it('known OL name in schema expression is accepted', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [x])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('unknown name in schema expression errors', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [unknown_thing])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable unknown_thing'));
  });

  it('Sort is always in scope in schemas', () => {
    expect(errors(
      'schema\nfoo = fun s => (Ok [Sort])\nend'
    )).toEqual([]);
  });

  it('construct declarations not visible in preceding schema', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [y])',
      'construct by foo', 'y : x',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable y'));
  });

  it('?-prefixed variables in OL patterns are not scope-checked', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | [(name, params, anything)] => (Ok [anything])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('deeply nested OL application in pattern scope-checks all identifiers', () => {
    const code = [
      'postulate', 'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      'schema',
      'foo = fun s => match s with',
      '  | [(f, [], eq ret ret f (refl ret body))]',
      '    => (Ok [body])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('standalone schema without OL context is permissive', () => {
    // No postulate context → permissive mode, bare identifiers accepted as Term
    expect(errors('schema\nfoo = fun s => (Ok [x])\nend')).toEqual([]);
  });

  it('schema with OL context is strict', () => {
    // With postulate → strict mode, unknown identifiers error
    const msgs = errorMessages(
      'postulate\ny : Sort\nschema\nfoo = fun s => (Ok [x])\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable x'));
  });

  it('unbound in expression position errors when OL scope is set', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [unbound])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable unbound'));
  });
});

/* ------------------------------------------------------------------ */
/*  ML holes                                                           */
/* ------------------------------------------------------------------ */

describe('ML holes', () => {
  it('hole as schema body gets schema type as goal', () => {
    const h = holes('schema\nfoo = ?\nend');
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    // Schema type is expanded (no "Signature" shorthand)
    expect(goal).toContain('String');
    expect(goal).toContain('->');
    expect(goal).toContain('Result');
  });

  it('multiple holes each get separate info', () => {
    const code = 'schema\nfoo = fun s => match s with | _ => (Ok [?, ?]) end\nend';
    const h = holes(code);
    expect(h.length).toBe(2);
  });

  it('hole in Error argument gets String as goal', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with | _ => (Error ?) end',
      'construct by foo', 'y : x',
      'end',
    ].join('\n');
    const h = holes(code);
    const mlHoles = h.filter(([_, info]) => printTerm(info.goal) === 'String');
    expect(mlHoles.length).toBe(1);
  });

  it('ML hole context includes OL bindings from postulate', () => {
    const code = [
      'postulate', 'x : Sort', 'y : x',
      'schema', 'foo = ?',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBe(1);
    const ctx = h[0][1].context;
    expect(ctx.size).toBeGreaterThanOrEqual(2); // at least x and y
  });

  it('hole in fun parameter is accepted as wildcard', () => {
    expect(errors(
      'schema\nfoo = fun ? => (Ok [])\nend'
    )).toEqual([]);
  });

  it('hole in function position of application has goal and context', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | _ => (Ok [(? x)])',
      '  end',
      'end',
    ].join('\n');
    const h = holes(code);
    // The ? in (? x) is in function position — should still produce a hole
    expect(h.length).toBeGreaterThanOrEqual(1);
    // Each hole should have a context
    h.forEach(([_, info]) => {
      expect(info.context).toBeDefined();
    });
  });

  it('hole as bare expression in Ok list has goal Term', () => {
    const h = holes('schema\nfoo = fun s => (Ok [?]) end\nend');
    expect(h.length).toBe(1);
    expect(printTerm(h[0][1].goal)).toBe('Term');
  });

  it('hole in function position of OL application has goal and context', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => (Ok [(?)])',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('hole in scrutinee of match has goal and context', () => {
    const code = 'schema\nfoo = fun s => match ? with | _ => (Ok []) end\nend';
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('hole in condition of if has goal and context', () => {
    const code = 'schema\nfoo = fun s => (if ? then (Ok []) else (Error "bad") end)\nend';
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('every ML hole always has a context', () => {
    const code = [
      'postulate', 'x : Sort', 'y : x',
      'schema',
      'foo = fun s => match s with',
      '  | [(name, params, ret)] => (Ok [?, (? ret)])',
      '  | _ => (Error ?)',
      '  end',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(3);
    h.forEach(([_, info]) => {
      expect(info.context).toBeDefined();
      expect(info.context.size).toBeGreaterThanOrEqual(2); // at least x, y from postulate
    });
  });
});

/* ------------------------------------------------------------------ */
/*  Total error localization in ML checker                             */
/* ------------------------------------------------------------------ */

describe('ML total error localization', () => {
  it('reports errors in multiple match branches, not just the first', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | [] => "wrong1"',
      '  | _ => "wrong2"',
      '  end',
      'end',
    ].join('\n');
    const errs = errors(code);
    // Both branches have type errors — should report at least 2
    expect(errs.length).toBeGreaterThanOrEqual(2);
  });

  it('reports errors in both if branches', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => (if s == s then "wrong1" else "wrong2" end)',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(2);
  });

  it('reports hole AND error in same expression', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | _ => (Ok [?, badvar])',
      '  end',
      'end',
    ].join('\n');
    const result = check(code);
    // Should have both: a hole for ? AND an error for badvar
    expect(result.holes.length).toBeGreaterThanOrEqual(1);
    expect(result.errors.length).toBeGreaterThanOrEqual(1);
    expect(result.errors).toContainEqual(
      expect.objectContaining({ message: expect.stringContaining('Unbound variable badvar') })
    );
  });

  it('error in scrutinee does not prevent checking branches', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match badvar with',
      '  | _ => "also wrong"',
      '  end',
      'end',
    ].join('\n');
    const errs = errors(code);
    // Should report both: badvar unbound AND branch type error
    expect(errs.length).toBeGreaterThanOrEqual(2);
  });

  it('multiple unbound variables each get their own error', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => (Ok [bad1, bad2, bad3])',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(3);
  });

  it('error in list element does not prevent checking other elements', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => (Ok [x, badvar, x])',
      'end',
    ].join('\n');
    const errs = errors(code);
    // badvar is the only error — x is fine
    expect(errs.length).toBe(1);
    expect(errs[0].message).toContain('badvar');
  });
});

/* ------------------------------------------------------------------ */
/*  Context isolation and flow                                         */
/* ------------------------------------------------------------------ */

describe('context isolation', () => {
  it('schema bindings do NOT leak into construct', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [])',
      'construct by foo',
      'y : foo',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('construct declarations see earlier construct declarations', () => {
    const code = [
      'postulate', 'x : Sort',
      'construct by foo',
      'y : x', 'z : y', 'w : z',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('standalone schema with no postulate context works', () => {
    expect(errors(
      'schema\nfoo = fun s => match s with | _ => (Ok []) end\nend'
    )).toEqual([]);
  });

  it('empty schema body does not crash', () => {
    expect(() => errors('schema\nend')).not.toThrow();
  });

  it('empty construct body does not crash', () => {
    expect(errors('postulate\nx : Sort\nconstruct by foo\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  fun...=>f morph parser interactions                                */
/* ------------------------------------------------------------------ */

describe('fun morph parser', () => {
  it('fun inside schema does not capture block end', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [])',
      'construct by foo', 'y : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('nested fun inside match works', () => {
    const code = [
      'schema',
      'foo = fun s => match s with',
      '  | _ => fun x => (Ok []) end',
      'end',
    ].join('\n');
    // fun x => (Ok []) is the match body, then end closes the match
    expect(() => errors(code)).not.toThrow();
  });

  it('match => inside fun body uses unmorphed =>', () => {
    const code = [
      'schema',
      'foo = fun s => match s with | x => (Ok []) | _ => (Error "bad") end',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Schema annotation edge cases                                       */
/* ------------------------------------------------------------------ */

describe('schema annotation edge cases', () => {
  it('hole in type annotation is invalid', () => {
    const msgs = errorMessages(
      'schema\nfoo : (? -> (Result (List Term))) = fun s => (Ok [])\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Invalid type annotation'));
  });

  it('correct annotation with wrong body reports only body error', () => {
    const code = [
      'schema',
      'foo : ((List Signature) -> (Result (List Term))) = fun s => "wrong"',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.length).toBeGreaterThan(0);
    const mismatch = msgs.filter(m => m.includes('Schema type mismatch'));
    expect(mismatch).toEqual([]);
  });

  it('unknown type name in annotation is invalid', () => {
    const msgs = errorMessages('schema\nfoo : UnknownType = fun s => (Ok [])\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Invalid type annotation'));
  });

  it('Signature shorthand in annotation is accepted', () => {
    expect(errors(
      'schema\nfoo : ((List Signature) -> (Result (List Term))) = fun s => (Ok [])\nend'
    )).toEqual([]);
  });

  it('pair type annotation errors as schema mismatch', () => {
    const msgs = errorMessages('schema\nfoo : (Bool, String) = fun s => (Ok [])\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Schema type mismatch'));
  });
});

/* ------------------------------------------------------------------ */
/*  Shared namespace: OL and ML bindings in one context                */
/* ------------------------------------------------------------------ */

describe('shared namespace', () => {
  it('OL postulate names are visible inside schema body', () => {
    const code = [
      'postulate', 'U : Sort', '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      'schema', 'foo = fun s => (Ok [eq U U Sort Sort])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('OL name not in scope produces error in schema body', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema', 'foo = fun s => (Ok [nonexistent])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable nonexistent'));
  });

  it('ML pattern variable x usable in schema body expression', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | [(name, [], ret)] => (Ok [ret])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('ML hole in schema sees OL context', () => {
    const code = [
      'postulate', 'x : Sort', 'y : x',
      'schema', 'foo = ?',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBe(1);
    const ctx = h[0][1].context;
    // Should contain both x and y from the postulate
    expect(ctx.has('x')).toBe(true);
    expect(ctx.has('y')).toBe(true);
  });

  it('ML hole in match branch sees pattern bindings AND OL context', () => {
    const code = [
      'postulate', 'x : Sort',
      'schema',
      'foo = fun s => match s with',
      '  | [(name, [], ret)] => (Ok [?])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBe(1);
    const ctx = h[0][1].context;
    // Should have OL binding x and ML bindings name, ret, s
    expect(ctx.has('x')).toBe(true);
  });

  it('postulate context flows through to construct after schema', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      'D : U', 'K : D', 'S : D',
      '(ap (f : D) (a : D)) : D',
      'schema',
      'definition = fun s => match s with',
      '  | [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid")',
      '  end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  ML type display round-trip (property-based)                        */
/* ------------------------------------------------------------------ */

describe('ML type display round-trip', () => {
  // Generate random ML type strings that should round-trip through parseAndPrint.
  // Mirrors the grammar of mlType: atoms, List/Result/Arrow/Pair applied recursively.
  const mlTypeArb: fc.Arbitrary<string> = fc.letrec(tie => ({
    atom: fc.constantFrom('Term', 'Sort', 'Bool', 'String'),
    pair: fc.tuple(tie('type') as fc.Arbitrary<string>, tie('type') as fc.Arbitrary<string>)
      .map(([a, b]) => `(${a}, ${b})`),
    list: (tie('type') as fc.Arbitrary<string>).map(t => `(List ${wrap(t)})`),
    result: (tie('type') as fc.Arbitrary<string>).map(t => `(Result ${wrap(t)})`),
    arrow: fc.tuple(tie('type') as fc.Arbitrary<string>, tie('type') as fc.Arbitrary<string>)
      .map(([a, b]) => `(${wrap(a)} -> ${wrap(b)})`),
    type: fc.oneof(
      { weight: 4, arbitrary: tie('atom') as fc.Arbitrary<string> },
      { weight: 1, arbitrary: tie('pair') as fc.Arbitrary<string> },
      { weight: 2, arbitrary: tie('list') as fc.Arbitrary<string> },
      { weight: 2, arbitrary: tie('result') as fc.Arbitrary<string> },
      { weight: 1, arbitrary: tie('arrow') as fc.Arbitrary<string> },
    ),
  })).type;

  // Wrap non-atomic type strings in parens
  function wrap(s: string): string {
    // Already wrapped or single identifier
    if (s.startsWith('(') || /^[A-Za-z]+$/.test(s)) return s;
    return `(${s})`;
  }

  it('mlTypeToTerm round-trips through parseAndPrint', () => {
    fc.assert(fc.property(mlTypeArb, (typeStr: string) => {
      // Place the type string as a schema body hole goal context:
      // schema body with annotation = parseAndPrint should equal itself
      const pp = parseAndPrint(typeStr) as string;
      const pp2 = parseAndPrint(pp) as string;
      expect(pp2).toBe(pp);
    }), { numRuns: 200 });
  });

  it('ML hole goals round-trip through parseAndPrint', () => {
    // Specific types that exercise nesting
    const types = [
      'Result (List Term)',
      '(List (String, Term)) -> (Result (List Term))',
      'List (List (String, Term), Term)',
      '(List (List (String, Term), Term)) -> (Result (List Term))',
      'List (Result (List (String, Term)))',
    ];
    for (const t of types) {
      const pp = parseAndPrint(t) as string;
      const pp2 = parseAndPrint(pp) as string;
      expect(pp2).toBe(pp);
    }
  });

  it('schema hole goals round-trip', () => {
    // The actual schema type, displayed via mlTypeToTerm
    const code = 'schema\nfoo = ?\nend';
    const h = holes(code);
    expect(h.length).toBe(1);
    const goalStr = printTerm(h[0][1].goal);
    const roundTripped = parseAndPrint(goalStr) as string;
    expect(roundTripped).toBe(goalStr);
  });
});
