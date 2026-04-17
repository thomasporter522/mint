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
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });

  it('reports inconsistency for genuinely wrong types', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\ny : x\n(f (a : Sort)) : Sort\ng : (f y)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });
});

/* ------------------------------------------------------------------ */
/*  Dependent return type substitution                                 */
/* ------------------------------------------------------------------ */

describe('return type substitution', () => {
  it('declared type is the annotation, not the return type of an application', () => {
    // f : (a : Sort) -> a.  g : (f Sort).
    // g has type (f Sort), NOT Sort. (f Sort) ≠ Sort — they are different terms.
    // So (f g) should fail: f expects type Sort, but g has type (f Sort).
    const msgs = errorMessages(
      'postulate\nx : Sort\n(f (a : Sort)) : a\ng : (f Sort)\na : (f g)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
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
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
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
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
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

  it('return type with holes is consistent when structure matches', () => {
    // (trans D ? ? ? ? ?) has return type (eq D D ? ?) which is consistent with (eq D D x y)
    expect(errors(
      'postulate\nU : Sort\n(eq (A : U) (B : U) (a : A) (b : B)) : U\n(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)\nD : U\nx : D\ny : (eq D D x x)\nz : (eq (eq D D x x) (eq D D x x) y (trans D ? ? ? ? ?))\nend'
    )).toEqual([]);
  });

  it('expression with holes is inconsistent when structure differs', () => {
    // (eq (eq ? ? ? ?) (eq ? ? ? ?) ? ?) is NOT consistent with (eq D D x y)
    // because the first args are eq-applications vs D
    const msgs = errorMessages(
      'postulate\nU : Sort\n(eq (A : U) (B : U) (a : A) (b : B)) : U\n(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)\nD : U\nx : D\ny : (eq D D x x)\nz : (eq (eq D D x x) (eq D D x x) y (trans (eq ? ? ? ?) ? ? ? ? ?))\nend'
    );
    expect(msgs.length).toBeGreaterThan(0);
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
      'y : x',
      'meta',
      'schema foo = fun s => match s with | [(name, [], ret)] => (Ok [y]) | _ => (Error "bad") end',
      'construct by foo',
      'z : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('reports ML type error in schema body', () => {
    const code = [
      'postulate',
      'x : Sort',
      'meta',
      'schema foo = fun s => match s with | _ => "wrong" end',
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
      'meta',
      'schema foo = fun s => match s with | _ => x end',
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
      'y : x',
      'meta',
      'schema foo = fun s => match s with | [(name, [], ret)] => (Ok [y]) | _ => (Error "bad") end',
      'construct by foo',
      'z : x',
      'end',
    ].join('\n');
    // Schema returns y as witness for z:x. y has type x, which matches z:x.
    expect(errors(code)).toEqual([]);
  });

  it('schema definition with non-function body produces type error', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\nmeta\nschema foo = x\nend'
    );
    // x is not a function (schema type), so this should error
    expect(msgs.length).toBeGreaterThan(0);
  });

  it('reports type annotation mismatch', () => {
    const msgs = errorMessages(
      'meta\nschema declaration : Bool = ?\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Schema type mismatch'));
  });

  it('accepts correct type annotation with parens', () => {
    const code = [
      'postulate',
      'x : Sort',
      'y : x',
      'meta',
      'schema foo : ((List Signature) -> (Result (List Term))) = fun s => match s with | [(name, [], ret)] => (Ok [y]) | _ => (Error "bad") end',
      'construct by foo',
      'z : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('accepts correct type annotation written out fully', () => {
    expect(errors(
      'meta\nschema declaration : ((List (Term, (List (Term, Term)), Term)) -> (Result (List Term))) = ?\nend'
    )).toEqual([]);
  });

  it('unknown identifier in OL pattern binds as pattern variable', () => {
    // Without ? convention, unknown identifiers in OL patterns are binders
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      'meta',
      'schema foo = fun s => match s with',
      '  | [(f, [], eq2 ret ret f body)] => (Ok [body])',
      '  | _ => (Error "bad")',
      '  end',
      'end',
    ].join('\n');
    // eq2 is not in scope but binds as a pattern variable — no error
    expect(errors(code)).toEqual([]);
  });

  it('schema errors do not leak into surrounding blocks', () => {
    const code = 'postulate\nU : Sort\nmeta\nschema declaration = fun x => ?\nend';
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
      'postulate\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\ny : x\nend'
    )).toEqual([]);
  });

  it('reports unbound variable in construct declaration', () => {
    const msgs = errorMessages(
      'postulate\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\ny : z\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('postulate context flows into construct declarations', () => {
    expect(errors(
      'postulate\nx : Sort\ny : x\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\nz : y\nend'
    )).toEqual([]);
  });

  it('full chain: postulate context flows through schema to construct', () => {
    const code = [
      'postulate',
      'x : Sort',
      'y : x',
      'z : y',
      'meta',
      'schema foo = fun s => match s with | [(name, [], ret)] => (Ok [z]) | _ => (Error "bad") end',
      'construct by foo',
      'w : y',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('construct declarations extend the context', () => {
    const code = [
      'postulate',
      'x : Sort',
      'meta',
      'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
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
      'meta',
      'schema definition =',
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

  it('definition + arg-definition schemas with full SKK proof', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)',
      'D : U', 'K : D', 'S : D',
      '(ap (f : D) (a : D)) : D',
      '(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
      '(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))',
      '(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))',
      'meta',
      'schema definition =',
      '  fun s => match s with',
      '  | [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid definition")',
      '  end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'meta',
      'schema arg-definition = fun s => match s with | [(f, params, ret), (f_eq, params, eq ret ret applied body)] => if applied == (foldl (fun acc => fun p => match p with | (x, t) => (acc x) end) f params) then (Ok [body, (refl ret body)]) else (Error "LHS mismatch") end | _ => (Error "invalid arg-definition") end',
      'construct by arg-definition',
      '(ap-I (x : D)) : (eq D D (ap I x) x)',
      '(ap-I-pf (x : D)) : (eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (',
      '  trans D',
      '  (ap I x) (ap (ap (ap S K) K) x) x',
      '  (ap-cong I (ap (ap S K) K) x I-eq)',
      '  (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x',
      '  (ap-S K K x)',
      '  (ap-K x (ap K x)))))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('full equational proof: ap-I reduction via trans/ap-cong', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)',
      '',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      '(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
      '(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))',
      '(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))',
      'meta',
      'schema definition =',
      '  fun s => match s with',
      '  | [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid definition")',
      '  end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'meta',
      'schema arg-definition = fun s => match s with | [(f, params, ret), (f_eq, params, eq ret ret applied body)] => if applied == (foldl (fun acc => fun p => match p with | (x, t) => (acc x) end) f params) then (Ok [body, (refl ret body)]) else (Error "LHS mismatch") end | _ => (Error "invalid") end',
      'construct by arg-definition',
      '(ap-I (x : D)) : (eq D D (ap I x) x)',
      '(ap-I-pf (x : D)) : (eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (',
      '  trans D',
      '  (ap I x) (ap (ap (ap S K) K) x) x',
      '  (ap-cong I (ap (ap S K) K) x I-eq)',
      '  (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x',
      '  (ap-S K K x)',
      '  (ap-K x (ap K x)))))',
      'end',
    ].join('\n');
    // Type-checker warnings about foldl are OK, but no OL or witness errors
    expect(errors(code)).toEqual([]);
  });

  it('both schemas in single meta block with full proof', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)',
      '',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      '(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
      '(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))',
      '(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))',
      'meta',
      'schema definition =',
      '  fun s => match s with',
      '  | [(f, [], ret),',
      '     (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid definition")',
      '  end',
      'schema arg-definition = fun s => match s with | [(f, params, ret), (f_eq, params, eq ret ret applied body)] => if applied == (foldl (fun acc => fun p => match p with | (x, t) => (acc x) end) f params) then (Ok [body, (refl ret body)]) else (Error "LHS mismatch") end | _ => (Error "invalid arg-definition") end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'construct by arg-definition',
      '(ap-I (x : D)) : (eq D D (ap I x) x)',
      '(ap-I-pf (x : D)) : (eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (',
      '  trans D',
      '  (ap I x) (ap (ap (ap S K) K) x) x',
      '  (ap-cong I (ap (ap S K) K) x I-eq)',
      '  (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x',
      '  (ap-S K K x)',
      '  (ap-K x (ap K x)))))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('arg-definition schema produces correct witnesses for parameterized declarations', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)',
      '',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      '(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)',
      '(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))',
      '(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))',
      'meta',
      'schema definition =',
      '  fun s => match s with',
      '  | [(f, [], ret), (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl ret body)])',
      '  | _ => (Error "invalid definition")',
      '  end',
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'meta',
      'schema arg-definition = fun s => match s with | [(f, params, ret), (f_eq, params, eq ret ret applied body)] => if applied == (foldl (fun acc => fun p => match p with | (x, t) => (acc x) end) f params) then (Ok [body, (refl ret body)]) else (Error "LHS mismatch") end | _ => (Error "invalid arg-definition") end',
      'construct by arg-definition',
      '(ap-I (x : D)) : (eq D D (ap I x) x)',
      '(ap-I-pf (x : D)) : (eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (',
      '  trans D',
      '  (ap I x) (ap (ap (ap S K) K) x) x',
      '  (ap-cong I (ap (ap S K) K) x I-eq)',
      '  (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x',
      '  (ap-S K K x)',
      '  (ap-K x (ap K x)))))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Witness-and-discard: schema execution on construct blocks          */
/*  These tests prepare for the implementation of running schemas on   */
/*  construct declarations and type-checking the produced witnesses.   */
/* ------------------------------------------------------------------ */

describe('witness-and-discard (future: schema execution)', () => {
  // Helper: the standard postulate + definition schema preamble
  const preamble = [
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
    'meta',
    'schema definition =',
    '  fun s => match s with',
    '  | [(f, [], ret),',
    '     (f_eq, [], eq ret ret f body)]',
    '      => (Ok [body, (refl ret body)])',
    '  | _ => (Error "invalid definition")',
    '  end',
  ];

  it('correct construct block matching definition schema has no errors', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  // --- Circular / self-referential witnesses ---

  it('should fail: equation I = I produces circular witness', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      // eq D D I I means "I = I" — the body IS I, making the witness self-referential
      'I-eq : (eq D D I I)',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBe(1);
    expect(errs[0].message).toContain('ill-typed witnesses');
  });

  // --- Construct block structural mismatches ---

  it('should fail: three declarations instead of two', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'extra : D',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: one declaration instead of two', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: equation sides swapped in construct block', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      'I-eq : (eq D D (ap (ap S K) K) I)',
      'end',
    ].join('\n');
    // Pattern matches but with f=(ap (ap S K) K) and body=I,
    // producing wrong witnesses that won't type-check
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: second declaration is not an equation', () => {
    const code = [
      ...preamble,
      'construct by definition',
      'I : D',
      'I-val : D',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: declarations have parameters but schema expects []', () => {
    const code = [
      ...preamble,
      'construct by definition',
      '(I (x : D)) : D',
      'I-eq : (eq D D (I K) (ap (ap S K) K))',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  // --- Schema produces ill-typed witnesses ---

  it('should fail: schema produces witness of wrong type', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      'D : U',
      'K : D',
      'meta',
      'schema bad-schema =',
      '  fun s => match s with',
      '  | _ => (Ok [K, K])',
      '  end',
      'construct by bad-schema',
      'I : D',
      'I-eq : (eq D D I K)',
      'end',
    ].join('\n');
    // K : D but I-eq needs type (eq D D I K) — substituting K for I-eq is ill-typed
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: schema returns wrong number of witnesses', () => {
    const code = [
      'postulate',
      'U : Sort',
      'D : U',
      'K : D',
      'meta',
      'schema too-few =',
      '  fun s => match s with',
      '  | _ => (Ok [K])',
      '  end',
      'construct by too-few',
      'I : D',
      'J : D',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: schema returns Error for valid-looking input', () => {
    const code = [
      'postulate',
      'U : Sort',
      'D : U',
      'K : D',
      'meta',
      'schema always-fail =',
      '  fun s => match s with',
      '  | _ => (Error "nope")',
      '  end',
      'construct by always-fail',
      'I : D',
      'end',
    ].join('\n');
    expect(errors(code).length).toBeGreaterThan(0);
  });

  // --- Schema itself has subtle errors ---

  it('should fail: schema pattern binds wrong component as equation', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      'meta',
      'schema buggy-def =',
      '  fun s => match s with',
      '  | [(f, [], ret),',
      '     (f_eq, [], eq ret ret f body)]',
      '      => (Ok [body, (refl body body)])',
      '  | _ => (Error "invalid")',
      '  end',
      'construct by buggy-def',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'end',
    ].join('\n');
    // (refl body body) produces wrong type — witness for I-eq is ill-typed
    expect(errors(code).length).toBeGreaterThan(0);
  });

  it('should fail: schema swaps witness order', () => {
    const code = [
      'postulate',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      'D : U',
      'K : D',
      'S : D',
      '(ap (f : D) (a : D)) : D',
      'meta',
      'schema swapped-def =',
      '  fun s => match s with',
      '  | [(f, [], ret),',
      '     (f_eq, [], eq ret ret f body)]',
      '      => (Ok [(refl ret body), body])',
      '  | _ => (Error "invalid")',
      '  end',
      'construct by swapped-def',
      'I : D',
      'I-eq : (eq D D I (ap (ap S K) K))',
      'end',
    ].join('\n');
    // First witness is a proof but I : D expects type D
    expect(errors(code).length).toBeGreaterThan(0);
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
      'meta', 'schema foo = fun s => (Ok [x])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('unknown name in schema expression errors', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [unknown_thing])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable unknown_thing'));
  });

  it('Sort is always in scope in schemas', () => {
    expect(errors(
      'meta\nschema foo = fun s => (Ok [Sort])\nend'
    )).toEqual([]);
  });

  it('construct declarations not visible in preceding schema', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [y])',
      'construct by foo', 'y : x',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable y'));
  });

  it('?-prefixed variables in OL patterns are not scope-checked', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => match s with',
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
      'meta',
      'schema foo = fun s => match s with',
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
    expect(errors('meta\nschema foo = fun s => (Ok [x])\nend')).toEqual([]);
  });

  it('schema with OL context is strict', () => {
    // With postulate → strict mode, unknown identifiers error
    const msgs = errorMessages(
      'postulate\ny : Sort\nmeta\nschema foo = fun s => (Ok [x])\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable x'));
  });

  it('unbound in expression position errors when OL scope is set', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [unbound])',
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
    const h = holes('meta\nschema foo = ?\nend');
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    // Schema type is expanded (no "Signature" shorthand)
    expect(goal).toContain('Term');
    expect(goal).toContain('->');
    expect(goal).toContain('Result');
  });

  it('multiple holes each get separate info', () => {
    const code = 'meta\nschema foo = fun s => match s with | _ => (Ok [?, ?]) end\nend';
    const h = holes(code);
    expect(h.length).toBe(2);
  });

  it('hole in Error argument gets String as goal', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => match s with | _ => (Error ?) end',
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
      'meta', 'schema foo = ?',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBe(1);
    const ctx = h[0][1].context;
    expect(ctx.size).toBeGreaterThanOrEqual(2); // at least x and y
  });

  it('hole in fun parameter is accepted as wildcard', () => {
    expect(errors(
      'meta\nschema foo = fun ? => (Ok [])\nend'
    )).toEqual([]);
  });

  it('hole in function position of application has goal and context', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => match s with',
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
    const h = holes('meta\nschema foo = fun s => (Ok [?]) end\nend');
    expect(h.length).toBe(1);
    expect(printTerm(h[0][1].goal)).toBe('Term');
  });

  it('hole in function position of OL application has goal and context', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => (Ok [(?)])',
      'end',
    ].join('\n');
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('hole in scrutinee of match has goal and context', () => {
    const code = 'meta\nschema foo = fun s => match ? with | _ => (Ok []) end\nend';
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('hole in condition of if has goal and context', () => {
    const code = 'meta\nschema foo = fun s => (if ? then (Ok []) else (Error "bad") end)\nend';
    const h = holes(code);
    expect(h.length).toBeGreaterThanOrEqual(1);
  });

  it('every ML hole always has a context', () => {
    const code = [
      'postulate', 'x : Sort', 'y : x',
      'meta',
      'schema foo = fun s => match s with',
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
      'meta',
      'schema foo = fun s => match s with',
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
      'meta',
      'schema foo = fun s => (if s == s then "wrong1" else "wrong2" end)',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(2);
  });

  it('reports hole AND error in same expression', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => match s with',
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
      'meta',
      'schema foo = fun s => match badvar with',
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
      'meta',
      'schema foo = fun s => (Ok [bad1, bad2, bad3])',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(3);
  });

  it('error in list element does not prevent checking other elements', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => (Ok [x, badvar, x])',
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
      'meta', 'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
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
      'meta', 'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
      'construct by foo',
      'y : x', 'z : y', 'w : z',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('standalone schema with no postulate context works', () => {
    expect(errors(
      'meta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nend'
    )).toEqual([]);
  });

  it('empty schema body does not crash', () => {
    expect(() => errors('meta\nend')).not.toThrow();
  });

  it('empty construct body does not crash', () => {
    expect(errors('postulate\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  fun...=>f morph parser interactions                                */
/* ------------------------------------------------------------------ */

describe('fun morph parser', () => {
  it('fun inside schema does not capture block end', () => {
    const code = [
      'postulate', 'x : Sort', 'y : x',
      'meta', 'schema foo = fun s => match s with | [(name, [], ret)] => (Ok [y]) | _ => (Error "bad") end',
      'construct by foo', 'z : x',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('nested fun inside match works', () => {
    const code = [
      'meta',
      'schema foo = fun s => match s with',
      '  | _ => fun x => (Ok []) end',
      'end',
    ].join('\n');
    // fun x => (Ok []) is the match body, then end closes the match
    expect(() => errors(code)).not.toThrow();
  });

  it('match => inside fun body uses unmorphed =>', () => {
    const code = [
      'meta',
      'schema foo = fun s => match s with | x => (Ok []) | _ => (Error "bad") end',
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
      'meta\nschema foo : (? -> (Result (List Term))) = fun s => (Ok [])\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Invalid type annotation'));
  });

  it('correct annotation with wrong body reports only body error', () => {
    const code = [
      'meta',
      'schema foo : ((List Signature) -> (Result (List Term))) = fun s => "wrong"',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.length).toBeGreaterThan(0);
    const mismatch = msgs.filter(m => m.includes('Schema type mismatch'));
    expect(mismatch).toEqual([]);
  });

  it('unknown type name in annotation is invalid', () => {
    const msgs = errorMessages('meta\nschema foo : UnknownType = fun s => (Ok [])\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Invalid type annotation'));
  });

  it('Signature shorthand in annotation is accepted', () => {
    expect(errors(
      'meta\nschema foo : ((List Signature) -> (Result (List Term))) = fun s => (Ok [])\nend'
    )).toEqual([]);
  });

  it('pair type annotation errors as schema mismatch', () => {
    const msgs = errorMessages('meta\nschema foo : (Bool, String) = fun s => (Ok [])\nend');
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
      'meta', 'schema foo = fun s => (Ok [eq U U Sort Sort])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('OL name not in scope produces error in schema body', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [nonexistent])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable nonexistent'));
  });

  it('ML pattern variable x usable in schema body expression', () => {
    const code = [
      'postulate', 'x : Sort',
      'meta',
      'schema foo = fun s => match s with',
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
      'meta', 'schema foo = ?',
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
      'meta',
      'schema foo = fun s => match s with',
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
      'meta',
      'schema definition = fun s => match s with',
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
    const code = 'meta\nschema foo = ?\nend';
    const h = holes(code);
    expect(h.length).toBe(1);
    const goalStr = printTerm(h[0][1].goal);
    const roundTripped = parseAndPrint(goalStr) as string;
    expect(roundTripped).toBe(goalStr);
  });
});
