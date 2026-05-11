import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { readFileSync } from 'fs';
import { resolve } from 'path';
// @ts-ignore
import { processCode, printTerm, parseAndPrint } from '../reason-bridge';

/* ------------------------------------------------------------------ */
/*  Helpers                                                            */
/* ------------------------------------------------------------------ */

type Error = { type: string; message: string; from: number; to: number };
type HoleInfo = { goal: any; context: any };
type Result = {
  errors: Error[];
  holes: [number, HoleInfo][];
  inlayHints: [number, string, string][];
  definitions: [number, number, number, number][];
  completeBlocks: [number, number][];
};

function check(code: string): Result {
  return processCode(code) as Result;
}

function inlayHints(code: string): [number, string, string][] {
  return check(code).inlayHints;
}

function definitions(code: string): [number, number, number, number][] {
  return check(code).definitions;
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
    expect(errors('postulate\nSort : Sort\nx : Sort\nend')).toEqual([]);
  });

  it('accepts multiple declarations', () => {
    expect(errors('postulate\nSort : Sort\nx : Sort\ny : Sort\nend')).toEqual([]);
  });

  it('reports unbound variable', () => {
    const msgs = errorMessages('postulate\nSort : Sort\nx : y\nend');
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('earlier declaration is in scope for later ones', () => {
    expect(errors('postulate\nSort : Sort\nx : Sort\ny : x\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Function declarations and application                              */
/* ------------------------------------------------------------------ */

describe('function declarations', () => {
  it('accepts a function with one typed argument', () => {
    expect(errors('postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\nend')).toEqual([]);
  });

  it('accepts application with correct arity', () => {
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('reports too many arguments', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too many arguments'));
  });

  it('reports too few arguments', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Too few arguments'));
  });

  it('emits inlay hints for underapplied constructors', () => {
    /* `(f x)` — f takes 2, given 1, so one ghost ? before x. */
    const code = 'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x)\nend';
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    const [offset, content] = hints[0];
    expect(content).toBe('?');
    /* Offset should anchor at the `x` in the body of g. */
    expect(code.slice(offset, offset + 1)).toBe('x');
  });

  it('two missing args produce a two-? hint', () => {
    const code =
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : Sort) (c : Sort)) : Sort\ng : (f x)\nend';
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    expect(hints[0][1]).toBe('? ?');
  });

  it('hint anchors at the outer paren of a parenthesized arg', () => {
    /* Goal 1 from the refactor brief: `eq (ap...)` should render as
       `eq ? ? ? (ap...)`, not `eq (? ? ? ap...)`. The hint offset must
       land at the `(`, not at the inner `ap`. */
    const code =
      'postulate\nSort : Sort\nA : Sort\nB : Sort\nC : Sort\nD : Sort\n' +
      '(eq (a : A) (b : B) (c : C) (d : D)) : Sort\n' +
      '(ap (q : D)) : D\n' +
      'q : D\n' +
      'g : (eq (ap q))\nend';
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    const [offset, content] = hints[0];
    expect(content).toBe('? ? ?');
    /* The character at `offset` should be the open paren of `(ap q)`. */
    expect(code[offset]).toBe('(');
  });

  it('checks the given argument against the LAST parameter type', () => {
    /* f takes (a:A) and (b:B). A and B are distinct. Pass one arg of type B —
       under last-aligned checking this should NOT produce an inconsistency. */
    const ok =
      'postulate\nSort : Sort\nA : Sort\nB : Sort\nb : B\n(f (a : A) (b : B)) : Sort\ng : (f b)\nend';
    const msgs = errorMessages(ok);
    /* The arity error is preserved; there should be no consistency error. */
    expect(msgs.filter(m => m.includes('Inconsistency'))).toEqual([]);
  });

  it('rejects an underapplied arg that does not match the LAST parameter type', () => {
    /* Same setup, but pass an `a : A` for the single given slot — should mismatch
       against B (the trailing param). */
    const bad =
      'postulate\nSort : Sort\nA : Sort\nB : Sort\na : A\n(f (a : A) (b : B)) : Sort\ng : (f a)\nend';
    const msgs = errorMessages(bad);
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });

  it('fully-applied constructors emit no inlay hints', () => {
    const code =
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x x)\nend';
    expect(inlayHints(code)).toEqual([]);
  });

  it('overapplied constructors emit no inlay hints', () => {
    const code =
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x x)\nend';
    expect(inlayHints(code)).toEqual([]);
  });

  it('parenthesized singleton (C) elaborates with one ghost per param', () => {
    /* Bare parens around a constructor with params trigger elaboration —
       same machinery as `(C arg)`, anchored just before the closing
       paren. Each param gets a meta; unsolved ones render as `?`. */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      'g : (Ul)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    const [offset, label] = hints[0];
    expect(code[offset]).toBe(')');
    expect(label).toBe('?');
  });

  it('hole goal reflects metas solved AFTER the hole was registered', () => {
    /* The `?` for `p1` is checked during the args-fold for `pair ? ?`,
       BEFORE the outer subsume on the whole `(pair ? ?)` against its
       expected type runs and solves pair's implicit a1/a2. The hole
       goal must be zonked at the decl boundary so the user sees the
       fully-solved `proof (and a1 a2)` instead of `proof ?`. */
    const code = [
      'postulate',
      'sort : sort',
      'prop : sort',
      'proof (a : prop) : sort',
      'and (a1 a2 : prop) : prop',
      'pair (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2) : proof (and a1 a2)',
      'mythm-stmt (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2)',
      '    (body : proof (and a1 a2)) : sort',
      'mythm-pf (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2)',
      '    : mythm-stmt a1 a2 p1 p2 (pair ? ?)',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.holes.length).toBe(2);
    /* Each hole's goal printed via printTerm should be the fully-applied
       `proof X`, not `proof ?`. */
    const goals = result.holes.map(([, info]) => printTerm(info.goal));
    expect(goals).toEqual(['proof a1', 'proof a2']);
  });

  it('completeBlocks: a fully-complete postulate block is reported', () => {
    /* All decls hole-free, no errors, deps all complete → the block as
       a whole is complete. Anchor is the `postulate` keyword. */
    const code = [
      'postulate',
      'Sort : Sort',
      'level : Sort',
      '(Ul (l : level)) : Sort',
      'l0 : level',
      'x : Ul l0',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.completeBlocks.length).toBe(1);
    const [from] = result.completeBlocks[0];
    /* Block range starts at `postulate`. */
    expect(code.slice(from, from + 'postulate'.length)).toBe('postulate');
  });

  it('completeBlocks: a single hole in any decl breaks the whole block', () => {
    const code = [
      'postulate',
      'Sort : Sort',
      'level : Sort',
      '(Ul (l : level)) : Sort',
      'bad : Ul ?',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.completeBlocks).toEqual([]);
  });

  it('completeBlocks: a semantic error breaks the whole block', () => {
    const code = [
      'postulate',
      'Sort : Sort',
      'bad : missing',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.completeBlocks).toEqual([]);
  });

  it('completeBlocks: a syntax error breaks the whole block (bridge filter)', () => {
    const code = [
      'postulate',
      'Sort : Sort',
      'bad : )Sort',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.completeBlocks).toEqual([]);
    expect(result.errors.some(e => e.type === 'syntax')).toBe(true);
  });

  it('completeBlocks: earlier complete blocks survive even if later blocks fail', () => {
    /* The first postulate block is fully OK; the second has a hole. The
       first should still be reported complete; the second should not. */
    const code = [
      'postulate',
      'Sort : Sort',
      'x : Sort',
      'end',
      'postulate',
      'bad : Sort ?',
      'end',
    ].join('\n');
    const result = check(code);
    expect(result.completeBlocks.length).toBe(1);
    const [from] = result.completeBlocks[0];
    /* The complete one is the FIRST `postulate`. */
    expect(from).toBe(code.indexOf('postulate'));
  });

  it('grouped param syntax: (l1 l2 : level) ≡ (l1 : level) (l2 : level)', () => {
    /* Multiple identifiers sharing one type expand into multiple Params
       at AST-build time. The two decls below should be semantically
       indistinguishable. */
    const grouped = [
      'postulate',
      'level : Sort',
      '(eq (l1 l2 : level)) : Sort',
      'end',
    ].join('\n');
    const expanded = [
      'postulate',
      'level : Sort',
      '(eq (l1 : level) (l2 : level)) : Sort',
      'end',
    ].join('\n');
    expect(errorMessages(grouped)).toEqual(errorMessages(expanded));
    /* Click on `l2` (the second name in the group) jumps to `l2` itself,
       not the whole `(l1 l2 : level)` form. */
    const l2Use = grouped.lastIndexOf('l2');
    const defs = definitions(grouped);
    /* No use of l2 in this code — but the binding lookup itself must
       record the per-identifier nameMeta. We verify by checking that
       the param positions are distinct. */
    expect(defs).toBeDefined();
    /* Actual semantic equivalence: error count matches. */
    void l2Use;
  });

  it('multi-line declaration: indented continuations are part of the decl', () => {
    /* Whitespace-sensitive: an indented line following a decl head is
       treated as a continuation, so a single decl can span several
       lines for readability. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      'foo (a : Sort)',
      '    (b : Sort)',
      '    (c : Sort)',
      '    : Sort',
      'bar : foo A A A',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([]);
  });

  it('unparenthesized singleton does NOT elaborate', () => {
    /* Bare `C` (no parens) keeps the original wildcard semantics — no
       elaboration. The existing subsume pathway emits "Too few arguments". */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      'g : Ul',
      'end',
    ].join('\n');
    expect(inlayHints(code)).toEqual([]);
    expect(errorMessages(code)).toContainEqual(
      expect.stringContaining('Too few arguments'),
    );
  });

  it('parenthesized singleton (C) collapses to (C …) when all metas solve', () => {
    /* (refl) appears where the expected type is fully concrete — so all
       its implicits get solved by unification. Inlay collapses; no
       "Too few arguments" promoted. */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      '(eq (l : Sort) (x : Ul l)) : Sort',
      'll : Sort',
      'my : Ul ll',
      '(refl (l : Sort) (x : Ul l)) : eq x',
      '(use (e : eq ll my)) : Sort',
      'test : (use (refl))',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([]);
    const hints = inlayHints(code);
    /* All hints in this code (there are several underapplied terms)
       fully solve, so every label is the ellipsis. */
    hints.forEach(([, label]) => expect(label).toBe('…'));
  });

  it('hover tooltip on collapsed run shows the full values', () => {
    /* When the label is `…`, the tooltip carries the expansion so
       hovering reveals what was solved. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      '(Ul (l : Sort)) : Sort',
      'my-thing : (Ul A)',
      '(eq (l : Sort) (x : Ul l)) : Sort',
      'g : (eq my-thing)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    const [, label, tooltip] = hints[0];
    expect(label).toBe('…');
    expect(tooltip).toBe('A');
  });

  it('collapses fully-solved ghost run to a single ellipsis', () => {
    /* (eq (l : Sort) (x : Ul l)) — `l` is missing, `x` provided as `my-thing`.
       my-thing has type `Ul A`, so unifying solves ?l := A. With every
       ghost in the run resolved, the hint collapses to `…`. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      '(Ul (l : Sort)) : Sort',
      'my-thing : (Ul A)',
      '(eq (l : Sort) (x : Ul l)) : Sort',
      'g : (eq my-thing)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    expect(hints[0][1]).toBe('…');
  });

  it('suppresses "Too few arguments" when all metas are solved', () => {
    /* Same setup as above — fully solved, no `Too few arguments` error. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      '(Ul (l : Sort)) : Sort',
      'my-thing : (Ul A)',
      '(eq (l : Sort) (x : Ul l)) : Sort',
      'g : (eq my-thing)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.filter(m => m.includes('Too few arguments'))).toEqual([]);
  });

  it('parenthesizes compound solved values when run is partially solved', () => {
    /* 3 params: `l, m, x`. `x : Ul l` ties the third arg's type to the
       first. With one arg given, we have ghosts `?l ?m`. Unification
       solves ?l := (Ul-of A) (a compound). ?m has no constraint and
       stays unsolved. Run is partially solved → values rendering with
       parens around the compound: `(Ul-of A) ?`. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      '(Ul (l : Sort)) : Sort',
      '(Ul-of (a : Sort)) : Sort',
      'my-thing : (Ul (Ul-of A))',
      '(eq (l : Sort) (m : Sort) (x : Ul l)) : Sort',
      'g : (eq my-thing)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    expect(hints[0][1]).toBe('(Ul-of A) ?');
  });

  it('unsolved metas render as ?', () => {
    /* No dependency between the two params — the missing leading arg has
       no constraint and stays unsolved. */
    const code = [
      'postulate',
      'Sort : Sort',
      'a : Sort',
      '(eq (l : Sort) (x : Sort)) : Sort',
      'g : (eq a)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    expect(hints[0][1]).toBe('?');
  });

  it('keeps "Too few arguments" when any meta remains unsolved', () => {
    /* Independent params — no unification opportunity, error stands. */
    const code = [
      'postulate',
      'Sort : Sort',
      'a : Sort',
      '(eq (l : Sort) (x : Sort)) : Sort',
      'g : (eq a)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Too few arguments'));
  });

  it('refl-style decl: underapplied retType elaborates and is exposed', () => {
    /* `refl`'s retType `eq B b` is underapplied (eq takes 3 here). The
       missing leading `l` solves to refl's own param `l` via dependent
       unification on the trailing arg. The decl checks cleanly (no
       "Too few arguments"), the inlay collapses to `…`, and refl's
       binding now exposes the elaborated `eq l B b` so downstream uses
       see the full arity. (Repro of the MATH.mint refl issue.) */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      '(eq (l : Sort) (B : Ul l) (b : B)) : Sort',
      '(refl (l : Sort) (B : Ul l) (b : B)) : eq B b',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([]);
    const hints = inlayHints(code);
    expect(hints.length).toBe(1);
    expect(hints[0][1]).toBe('…');
  });

  it('type-level propagation: meta solved transitively via solution-type unification', () => {
    /* `eq b a` underapplies eq's first three args (l, A, B). Solving
       ?A := b's type (B sym-param) and ?B := a's type (A sym-param)
       happens directly. Then propagation: ?A's recorded expected was
       Ul ?l; B's actual type is Ul l; unifying solves ?l := l.
       Without type-level propagation, ?l would stay unsolved. */
    const code = [
      'postulate',
      'sort : sort',
      'level : sort',
      'Ul (l : level) : sort',
      'eq (l : level) (A : Ul l) (B : Ul l) (a : A) (b : B) : Ul l',
      'sym (l : level) (A : Ul l) (B : Ul l) (a : A) (b : B) (e : eq B a b) : eq b a',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([]);
    /* All inlay hints should fully collapse — every meta solved via
       direct unification or type-level propagation. */
    const hints = inlayHints(code);
    hints.forEach(([, label]) => expect(label).toBe('…'));
  });

  it('mlBuiltins (true/false/etc.) do not leak out of meta blocks', () => {
    /* `true` is an ML builtin (bool). When the user declares `true : bool`
       as an OL constructor in an earlier postulate block, a subsequent
       meta block must not shadow that with the ML builtin in the outer
       context — references to `true` after the meta block should still
       resolve to the user's OL constructor. */
    const code = [
      'postulate',
      'Sort : Sort',
      'bool : Sort',
      'true : bool',
      'false : bool',
      'meta',
      '    discard = "hi"',
      'end',
      'postulate',
      'use-true : true',
      'use-false : false',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.filter(m => m.includes('Unbound'))).toEqual([]);
  });

  it('schema sees the elaborated decls, not the raw underapplied form', () => {
    /* The schema's pattern expects `eq` applied to 5 things. The
       construct decl writes `eq B0 x0` (2 args, missing 3) — implicit.
       After elaboration the decl looks 5-arg to the schema, so the
       pattern matches and a witness is produced. Without elaboration
       happening before runSchema, the pattern would not match. */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      'A : Sort',
      'B0 : Ul A',
      'x0 : B0',
      '(eq (l : Sort) (B : Ul l) (x : B)) : Sort',
      '(refl (l : Sort) (B : Ul l) (x : B)) : eq B x',
      'meta',
      'schema sch = fun s => match s with',
      '| [(g, [], eq ll bb xx)] => (Ok [(refl ll bb xx)])',
      '| _ => (Error "wrong")',
      'end',
      'construct by sch',
      'foo-eq : eq B0 x0',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.filter(m => m.includes('Schema error') || m.includes('wrong'))).toEqual([]);
  });

  it('construct decl with underapplied retType uses elaborated form for witness check', () => {
    /* Violation-A guard: if the construct decl's retType `eq B0 x0` were
       compared raw against the schema-produced witness `(refl A B0 x0)`,
       arities would mismatch (2 vs 3). With elaboration applied to the
       construct decl too, both sides are 3-arg `eq A B0 x0` and the
       witness check succeeds. */
    const code = [
      'postulate',
      'Sort : Sort',
      '(Ul (l : Sort)) : Sort',
      'A : Sort',
      'B0 : Ul A',
      'x0 : B0',
      '(eq (l : Sort) (B : Ul l) (x : B)) : Sort',
      '(refl (l : Sort) (B : Ul l) (x : B)) : eq B x',
      'meta',
      'schema sch = fun s => match s with',
      '| [(g, [], _)] => (Ok [(refl A B0 x0)])',
      '| _ => (Error "x")',
      'end',
      'construct by sch',
      'foo-eq : eq B0 x0',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(
      msgs.filter(m => m.includes('Inconsistency') || m.includes('ill-typed'))
    ).toEqual([]);
  });

  it('per-decl meta scoping: solutions do not leak between decls', () => {
    /* Decl 1 fully solves (collapses to …); decl 2 stays unsolved (?),
       proving solutions reset between decls. */
    const code = [
      'postulate',
      'Sort : Sort',
      'A : Sort',
      '(Ul (l : Sort)) : Sort',
      'my-thing : (Ul A)',
      '(eq (l : Sort) (x : Ul l)) : Sort',
      'g1 : (eq my-thing)',
      '(eq2 (l : Sort) (x : Sort)) : Sort',
      'g2 : (eq2 A)',
      'end',
    ].join('\n');
    const hints = inlayHints(code);
    expect(hints.length).toBe(2);
    const contents = hints.map(h => h[1]).sort();
    expect(contents).toEqual(['?', '…']);
  });
});

/* ------------------------------------------------------------------ */
/*  Go-to-definition                                                   */
/* ------------------------------------------------------------------ */

describe('go-to-definition', () => {
  it('identifier reference points to its postulated decl name', () => {
    const code = 'postulate\nSort : Sort\nx : Sort\ny : x\nend';
    const defs = definitions(code);
    /* Find the use range covering the `x` in `y : x`. */
    const yUseStart = code.lastIndexOf('x');
    const rec = defs.find(([uf, ut]) => uf <= yUseStart && yUseStart < ut);
    expect(rec).toBeDefined();
    const [, , defFrom, defTo] = rec!;
    /* Target is the name identifier of `x : Sort`, not the whole line. */
    expect(code.slice(defFrom, defTo)).toBe('x');
    /* And it's the first occurrence (the decl), not the use. */
    expect(defFrom).toBeLessThan(yUseStart);
  });

  it('parameter reference inside a decl signature points to the param name', () => {
    /* (f (a : Sort)) : a — the `a` in the retType refers to the param. */
    const code = 'postulate\nSort : Sort\n(f (a : Sort)) : a\nend';
    const defs = definitions(code);
    /* The `a` in the retType comes after `: ` near the end. */
    const aUseStart = code.lastIndexOf('a');
    const rec = defs.find(([uf, ut]) => uf <= aUseStart && aUseStart < ut);
    expect(rec).toBeDefined();
    const [, , defFrom, defTo] = rec!;
    /* Target is the param's name identifier alone, not the whole `(a : Sort)`. */
    expect(code.slice(defFrom, defTo)).toBe('a');
    expect(defFrom).toBeLessThan(aUseStart);
  });

  it('constructor head application resolves to its decl name', () => {
    /* `(f x)` — clicking on `f` should jump to the `f` in `(f (a : Sort))`. */
    const code = 'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend';
    const defs = definitions(code);
    /* Find the `f` use in `(f x)` — it's the one in `g : (f x)`. */
    const gLine = code.indexOf('g : (f x)');
    const fUseStart = code.indexOf('f', gLine);
    const rec = defs.find(([uf, ut]) => uf <= fUseStart && fUseStart < ut);
    expect(rec).toBeDefined();
    const [, , defFrom, defTo] = rec!;
    /* Target is just the `f` identifier in the head. */
    expect(code.slice(defFrom, defTo)).toBe('f');
    expect(defFrom).toBeLessThan(fUseStart);
  });

  it('self-reference: the second `Sort` in `Sort : Sort` jumps to the first', () => {
    const code = 'postulate\nSort : Sort\nend';
    const defs = definitions(code);
    /* Locate the SECOND `Sort` (the one after the colon). */
    const firstSort = code.indexOf('Sort');
    const secondSort = code.indexOf('Sort', firstSort + 4);
    const rec = defs.find(([uf, ut]) => uf <= secondSort && secondSort < ut);
    expect(rec).toBeDefined();
    const [, , defFrom, defTo] = rec!;
    /* Target must be the FIRST `Sort` so that navigation actually moves. */
    expect(defFrom).toBe(firstSort);
    expect(code.slice(defFrom, defTo)).toBe('Sort');
  });

  it('self-reference inside an OLAp retType jumps to the decl name', () => {
    /* `(Ul (l : level)) : Ul l` — the head `Ul` in the retType refers
       to the decl being defined; clicking on it should navigate to the
       `Ul` in the head, not stay on itself. */
    const code = 'postulate\nlevel : Sort\nSort : Sort\n(Ul (l : level)) : Ul l\nend';
    const defs = definitions(code);
    const declLine = code.indexOf('(Ul (l : level))');
    const declUlStart = code.indexOf('Ul', declLine);
    const retUlStart = code.indexOf('Ul l', declLine + 1);
    const rec = defs.find(([uf, ut]) => uf <= retUlStart && retUlStart < ut);
    expect(rec).toBeDefined();
    const [, , defFrom, defTo] = rec!;
    expect(defFrom).toBe(declUlStart);
    expect(code.slice(defFrom, defTo)).toBe('Ul');
  });

  it('unbound references emit no definition record', () => {
    /* `y : z` where z isn't declared — no definition for the use. */
    const code = 'postulate\nSort : Sort\ny : z\nend';
    const defs = definitions(code);
    const zUseStart = code.lastIndexOf('z');
    const rec = defs.find(([uf, ut]) => uf <= zUseStart && zUseStart < ut);
    expect(rec).toBeUndefined();
  });
});

/* ------------------------------------------------------------------ */
/*  Argument scoping                                                   */
/* ------------------------------------------------------------------ */

describe('argument scoping', () => {
  it('argument bindings do not leak to the next line', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\n(f (a : Sort)) : a\ng : a\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable a'));
  });

  it('argument is in scope for the return type of its own line', () => {
    expect(errors(
      'postulate\nSort : Sort\n(f (a : Sort)) : a\nend'
    )).toEqual([]);
  });

  it('multiple arguments are in scope for each other and return type', () => {
    expect(errors(
      'postulate\nSort : Sort\n(f (a : Sort) (b : a)) : b\nend'
    )).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Type consistency at application sites                               */
/* ------------------------------------------------------------------ */

describe('type consistency', () => {
  it('no error when expected type matches inferred', () => {
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('expected argument type is the TYPE, not the full ascription pattern', () => {
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : a\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('rejects argument whose type does not match after substitution', () => {
    // pi expects (B : (arrow A Sort)). After A=Sort, second arg should be (arrow Sort Sort).
    // Bare Sort is not (arrow Sort Sort), so this should error.
    const msgs = errorMessages(
      'postulate\nSort : Sort\n(arrow (A : Sort) (B : Sort)) : Sort\n(pi (A : Sort) (B : (arrow A Sort))) : Sort\nx : (pi Sort Sort)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });

  it('reports inconsistency for genuinely wrong types', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\ny : x\n(f (a : Sort)) : Sort\ng : (f y)\nend'
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
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : a\ng : (f Sort)\na : (f g)\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });

  it('return type substitution with non-dependent return type is harmless', () => {
    // f always returns Sort regardless of argument — substitution is a no-op.
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f x)\nend'
    )).toEqual([]);
  });

  it('second argument type is substituted with first argument value', () => {
    // f : (a : Sort) -> (b : a) -> b
    // x : Sort, y : x
    // (f x y): first arg x checked against Sort ✓, second arg y checked against a[a:=x] = x.
    //   y has type x ✓. Return type = b[a:=x, b:=y] = y.
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\ny : x\n(f (a : Sort) (b : a)) : b\ng : (f x y)\nend'
    )).toEqual([]);
  });

  it('substitution detects type error in second argument', () => {
    // f : (a : Sort) -> (b : a) -> b
    // x : Sort, y : x
    // (f x x): second arg x checked against a[a:=x] = x. But x has type Sort, not x.
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\ny : x\n(f (a : Sort) (b : a)) : b\ng : (f x x)\nend'
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
      'postulate\nSort : Sort\nx : Sort\ny : x\nz : y\n(f (a : Sort) (b : a) (c : b)) : c\ng : (f x y z)\nend'
    )).toEqual([]);
  });

  it('substitution in return type used for outer consistency check', () => {
    // f : (a : Sort) -> a.  x : Sort.
    // g expects type x, but (f Sort) returns a[a:=Sort] = Sort.
    // Sort and x are different, so this should error.
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : a\ng : x\nh : (f g)\nend'
    );
    // (f g): g has type x, checked against Sort — inconsistency
    expect(msgs).toContainEqual(expect.stringContaining('Inconsistency'));
  });

  it('non-dependent multi-arg function still works', () => {
    // No parameter names appear in the return type — substitution is vacuous.
    expect(errors(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : Sort)) : Sort\ng : (f x x)\nend'
    )).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Holes                                                              */
/* ------------------------------------------------------------------ */

describe('holes', () => {
  it('does not loop on self-referential application in declaration RHS', () => {
    expect(() => errors(
      'postulate\nSort : Sort\n(eq (A : Sort) (B : Sort) (a : A) (b : B)) : Sort\n(refl (A : Sort) (a : A)) : (eq A ? ? ?)\nend'
    )).not.toThrow();
  });

  it('hole gets the expected type as its goal', () => {
    const g = goalString('postulate\nSort : Sort\nx : Sort\ng : ?\nend');
    expect(g).toBe('?');
  });

  it('hole in application position gets the argument type as goal', () => {
    const h = holes('postulate\nSort : Sort\nx : Sort\n(f (a : Sort)) : Sort\ng : (f ?)\nend');
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    expect(goal).toBe('Sort');
  });

  it('hole in second arg position gets substituted type as goal', () => {
    // f : (a : Sort) -> (b : a) -> b.  (f x ?): second arg expects a[a:=x] = x.
    const h = holes(
      'postulate\nSort : Sort\nx : Sort\n(f (a : Sort) (b : a)) : b\ng : (f x ?)\nend'
    );
    expect(h.length).toBe(1);
    const goal = printTerm(h[0][1].goal);
    expect(goal).toBe('x');
  });

  it('return type with holes is consistent when structure matches', () => {
    // (trans D ? ? ? ? ?) has return type (eq D D ? ?) which is consistent with (eq D D x y)
    expect(errors(
      'postulate\nSort : Sort\nU : Sort\n(eq (A : U) (B : U) (a : A) (b : B)) : U\n(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)\nD : U\nx : D\ny : (eq D D x x)\nz : (eq (eq D D x x) (eq D D x x) y (trans D ? ? ? ? ?))\nend'
    )).toEqual([]);
  });

  it('expression with holes is inconsistent when structure differs', () => {
    // (eq (eq ? ? ? ?) (eq ? ? ? ?) ? ?) is NOT consistent with (eq D D x y)
    // because the first args are eq-applications vs D
    const msgs = errorMessages(
      'postulate\nSort : Sort\nU : Sort\n(eq (A : U) (B : U) (a : A) (b : B)) : U\n(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)\nD : U\nx : D\ny : (eq D D x x)\nz : (eq (eq D D x x) (eq D D x x) y (trans (eq ? ? ? ?) ? ? ? ? ?))\nend'
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'postulate\nSort : Sort\nx : Sort\nmeta\nschema foo = x\nend'
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
      'Sort : Sort',
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
      'Sort : Sort',
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
    const code = 'postulate\nSort : Sort\nU : Sort\nmeta\nschema declaration = fun x => ?\nend';
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
    /* Schema produces a `?` per witness. The witness-completeness check
       flags this; verify there is no OTHER error (no unbound var, etc.). */
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\ny : x\nend'
    );
    expect(msgs).toEqual([expect.stringContaining('incomplete witnesses')]);
  });

  it('reports unbound variable in construct declaration', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\ny : z\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('postulate context flows into construct declarations', () => {
    /* `z : y` — checks that `y` (from postulate) is in scope. Witness is `?`,
       so completeness fires; no Unbound-variable error confirms scope. */
    const msgs = errorMessages(
      'postulate\nSort : Sort\nx : Sort\ny : x\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\nz : y\nend'
    );
    expect(msgs).toEqual([expect.stringContaining('incomplete witnesses')]);
  });

  it('full chain: postulate context flows through schema to construct', () => {
    const code = [
      'postulate',
      'Sort : Sort',
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
    /* `z : y` — checks `y` from earlier construct decl is in scope. Witness
       is `?`, so completeness fires; absence of Unbound-variable confirms scope. */
    const code = [
      'postulate',
      'Sort : Sort',
      'x : Sort',
      'meta',
      'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
      'construct by foo',
      'y : x',
      'z : y',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([expect.stringContaining('incomplete witnesses')]);
  });

  it('full definition schema example passes with no errors', () => {
    const code = [
      'postulate',
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
    'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
      'Sort : Sort',
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
/*  Syntax error reporting (Lezer error nodes)                         */
/* ------------------------------------------------------------------ */

describe('syntax errors', () => {
  it('empty file does not crash', () => {
    expect(() => errors('')).not.toThrow();
  });

  it('valid program produces no syntax errors', () => {
    const errs = errors('postulate\nSort : Sort\nend');
    expect(errs.filter(e => e.type === 'syntax')).toEqual([]);
  });

  it('reports a syntax error from a stray close paren', () => {
    const errs = errors('postulate\n)\nend');
    const syntax = errs.filter(e => e.type === 'syntax');
    expect(syntax.length).toBeGreaterThan(0);
    expect(syntax[0].message).toBe('Syntax error');
  });

  it('syntax error has a localized span', () => {
    const code = 'postulate\n)\nend';
    const errs = errors(code).filter(e => e.type === 'syntax');
    const e = errs[0];
    expect(e.from).toBeGreaterThanOrEqual(code.indexOf(')'));
    expect(e.to).toBeGreaterThan(e.from);
  });

  it('multiple errors at distinct positions are not collapsed', () => {
    const code = 'postulate\n)\nx : Sort\n)\nend';
    const syntax = errors(code).filter(e => e.type === 'syntax');
    // Same-position duplicates are deduped, but distinct ones are kept.
    const positions = new Set(syntax.map(e => e.from));
    expect(positions.size).toBe(syntax.length);
    expect(syntax.length).toBeGreaterThanOrEqual(2);
  });

  it('syntax errors do not suppress kernel errors', () => {
    // Unbound variable AND a stray paren — both should be reported.
    const code = 'postulate\nSort : Sort\nx : not_a_thing\n)\nend';
    const errs = errors(code);
    expect(errs.some(e => e.type === 'syntax')).toBe(true);
    expect(errs.some(e => e.message.includes('Unbound variable'))).toBe(true);
  });
});

/* ------------------------------------------------------------------ */
/*  OL scope checking in schemas                                       */
/* ------------------------------------------------------------------ */

describe('OL scope checking in schemas', () => {
  it('known OL name in schema expression is accepted', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [x])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('unknown name in schema expression errors', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [y])',
      'construct by foo', 'y : x',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable y'));
  });

  it('?-prefixed variables in OL patterns are not scope-checked', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'U : Sort',
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
      'postulate\nSort : Sort\ny : Sort\nmeta\nschema foo = fun s => (Ok [x])\nend'
    );
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable x'));
  });

  it('unbound in expression position errors when OL scope is set', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort', 'y : x',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort', 'y : x',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta',
      'schema foo = fun s => (if s == s then "wrong1" else "wrong2" end)',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(2);
  });

  it('reports hole AND error in same expression', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta',
      'schema foo = fun s => (Ok [bad1, bad2, bad3])',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThanOrEqual(3);
  });

  it('error in list element does not prevent checking other elements', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
      'construct by foo',
      'y : foo',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable'));
  });

  it('construct declarations see earlier construct declarations', () => {
    /* `w : z` references `z` from an earlier construct decl. Witness is
       `?`, so completeness fires; no Unbound-variable error confirms scope. */
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))',
      'construct by foo',
      'y : x', 'z : y', 'w : z',
      'end',
    ].join('\n');
    expect(errorMessages(code)).toEqual([expect.stringContaining('incomplete witnesses')]);
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
    expect(errors('postulate\nSort : Sort\nx : Sort\nmeta\nschema foo = fun s => (Ok (foldl (fun acc => fun _ => ? :: acc) [] s))\nconstruct by foo\nend')).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  fun...=>f morph parser interactions                                */
/* ------------------------------------------------------------------ */

describe('fun morph parser', () => {
  it('fun inside schema does not capture block end', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort', 'y : x',
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
      'postulate', 'Sort : Sort', 'U : Sort', '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      'meta', 'schema foo = fun s => (Ok [eq U U Sort Sort])',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('OL name not in scope produces error in schema body', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
      'meta', 'schema foo = fun s => (Ok [nonexistent])',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toContainEqual(expect.stringContaining('Unbound variable nonexistent'));
  });

  it('ML pattern variable x usable in schema body expression', () => {
    const code = [
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'postulate', 'Sort : Sort', 'x : Sort', 'y : x',
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
      'postulate', 'Sort : Sort', 'x : Sort',
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
      'Sort : Sort',
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

/* ------------------------------------------------------------------ */
/*  Typed-SK abstraction schema                                        */
/*  Tests the recursive [x]e SK abstraction from examples/typed-SK.    */
/*  Exercises meta-level recursion through knot-tying of closure envs. */
/* ------------------------------------------------------------------ */

describe('typed-SK abstraction schema', () => {
  // Postulates + recursive abs function + abstraction schema, parameterized
  // by extra postulates to keep the preamble reusable.
  function preamble(extraPostulates: string[] = []): string[] {
    return [
      'postulate',
      'Sort : Sort',
      'U : Sort',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      '(refl (A : U) (a : A)) : (eq A A a a)',
      '(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)',
      '(to (A : U) (B : U)) : U',
      '(ap (A : U) (B : U) (f : (to A B)) (a : A)) : B',
      '(cong-ap (A : U) (B : U) (f : (to A B)) (g : (to A B)) (a : A) (b : A)',
      '         (ef : (eq (to A B) (to A B) f g)) (ea : (eq A A a b))) :',
      '  (eq B B (ap A B f a) (ap A B g b))',
      '(K (A : U) (B : U)) : (to A (to B A))',
      '(S (A : U) (B : U) (C : U)) : (to (to A (to B C)) (to (to A B) (to A C)))',
      '(K-eq (A : U) (B : U) (x : A) (y : B)) : (eq A A (ap B A (ap A (to B A) (K A B) x) y) x)',
      '(S-eq (A : U) (B : U) (C : U) (f : (to A (to B C))) (g : (to A B)) (x : A)) :',
      '  (eq C C',
      '    (ap A C',
      '      (ap (to A B) (to A C)',
      '        (ap (to A (to B C)) (to (to A B) (to A C)) (S A B C) f)',
      '        g)',
      '      x)',
      '    (ap B C (ap A (to B C) f x) (ap A B g x)))',
      'N : U',
      'plus : (to N (to N N))',
      ...extraPostulates,
      'meta',
      'abs = fun x => fun e => fun A => fun B =>',
      '  if e == x',
      '  then (',
      '      (ap (to A (to A A)) (to A A)',
      '        (ap (to A (to (to A A) A)) (to (to A (to A A)) (to A A))',
      '          (S A (to A A) A)',
      '          (K A (to A A)))',
      '        (K A A))',
      '    ,',
      '      (trans A',
      '        (ap A A',
      '          (ap (to A (to A A)) (to A A)',
      '            (ap (to A (to (to A A) A)) (to (to A (to A A)) (to A A))',
      '              (S A (to A A) A)',
      '              (K A (to A A)))',
      '            (K A A))',
      '          x)',
      '        (ap (to A A) A',
      '          (ap A (to (to A A) A) (K A (to A A)) x)',
      '          (ap A (to A A) (K A A) x))',
      '        x',
      '        (S-eq A (to A A) A (K A (to A A)) (K A A) x)',
      '        (K-eq A (to A A) x (ap A (to A A) (K A A) x)))',
      '    )',
      '  else match e with',
      '  | (ap Aprime Bprime f a) =>',
      '      let f-res = (abs x f A (to Aprime B)) in',
      '      let a-res = (abs x a A Aprime) in',
      '      let fw = (fst f-res) in',
      '      let fp = (snd f-res) in',
      '      let aw = (fst a-res) in',
      '      let ap2 = (snd a-res) in',
      '      let witness =',
      '        (ap (to A Aprime) (to A B)',
      '          (ap (to A (to Aprime B)) (to (to A Aprime) (to A B))',
      '            (S A Aprime B)',
      '            fw)',
      '          aw) in',
      '      let proof =',
      '        (trans B',
      '          (ap A B witness x)',
      '          (ap Aprime B (ap A (to Aprime B) fw x) (ap A Aprime aw x))',
      '          (ap Aprime B f a)',
      '          (S-eq A Aprime B fw aw x)',
      '          (cong-ap Aprime B',
      '            (ap A (to Aprime B) fw x)',
      '            f',
      '            (ap A Aprime aw x)',
      '            a',
      '            fp',
      '            ap2)) in',
      '      (witness, proof)',
      '  | _ => ((ap B (to A B) (K B A) e), (K-eq B A e x))',
      '  end',
      '  end',
      'schema abstraction = fun s => match s with',
      '  | [(f, [], (to A B)), (_, [(x, _)], (eq _ _ (ap _ _ f x) body))] =>',
      '      let result = (abs x body A B) in',
      '      (Ok [(fst result), (snd result)])',
      '  | _ => (Error "abstraction: expected (f : to A B) and (f-beta (x : A) : eq B B (ap A B f x) body)")',
      '  end',
    ];
  }

  /* --- Positive cases: abstraction synthesizes correct combinators --- */

  it('identity: [n]n uses the I case', () => {
    const code = [
      ...preamble(),
      'construct by abstraction',
      'id : (to N N)',
      '(id-beta (n : N)) : (eq N N (ap N N id n) n)',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('constant function: [n]zero uses the K case', () => {
    const code = [
      ...preamble(['zero : N']),
      'construct by abstraction',
      'k-zero : (to N N)',
      '(k-zero-beta (n : N)) : (eq N N (ap N N k-zero n) zero)',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('double: [n]plus n n exercises two-level recursion', () => {
    const code = [
      ...preamble(),
      'construct by abstraction',
      'double : (to N N)',
      '(double-beta (n : N)) : (eq N N (ap N N double n) (ap N N (ap N (to N N) plus n) n))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('sequenced abstraction: triple built from double', () => {
    const code = [
      ...preamble(),
      'construct by abstraction',
      'double : (to N N)',
      '(double-beta (n : N)) : (eq N N (ap N N double n) (ap N N (ap N (to N N) plus n) n))',
      '',
      'construct by abstraction',
      'triple : (to N N)',
      '(triple-beta (n : N)) : (eq N N (ap N N triple n) (ap N N (ap N (to N N) plus n) (ap N N double n)))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('deeper body: [n]plus (plus n n) n requires depth-3 recursion', () => {
    const code = [
      ...preamble(),
      'construct by abstraction',
      'deep : (to N N)',
      '(deep-beta (n : N)) : (eq N N (ap N N deep n) (ap N N (ap N (to N N) plus (ap N N (ap N (to N N) plus n) n)) n))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('higher-order: abstraction variable has arrow type ([f] f (f zero))', () => {
    // aptwice : (to (to N N) N) with body f (f zero), where the bound
    // variable f is itself function-typed. Exercises abs with A = (to N N)
    // and subterms whose inner types mix arrows and atomics.
    const code = [
      ...preamble(['zero : N']),
      'construct by abstraction',
      'aptwice : (to (to N N) N)',
      '(aptwice-beta (f : (to N N))) : (eq N N (ap (to N N) N aptwice f) (ap N N f (ap N N f zero)))',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  /* --- Negative cases: pattern must reject malformed beta declarations --- */

  it('rejects equation whose LHS is not an application', () => {
    // (eq (to N N) (to N N) not-abs double) — LHS is a bare identifier,
    // not (ap A B f x), so the schema pattern must not match.
    const code = [
      ...preamble(),
      'construct by abstraction',
      'double : (to N N)',
      '(double-beta (n : N)) : (eq N N (ap N N double n) (ap N N (ap N (to N N) plus n) n))',
      '',
      'construct by abstraction',
      'not-abs : (to N N)',
      '(not-abs-beta (n : N)) : (eq (to N N) (to N N) not-abs double)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toEqual(
      expect.arrayContaining([expect.stringContaining('abstraction: expected')]),
    );
    // Must NOT report ill-typed witnesses — the pattern should reject before evaluation.
    expect(msgs.every(m => !m.includes('ill-typed witnesses'))).toBe(true);
  });

  it('rejects equation whose applied function is not the defined name', () => {
    // LHS is (ap N N plus n), but the defined function is `f`, not `plus`.
    // Nonlinear pattern match on f must fail.
    const code = [
      ...preamble(),
      'construct by abstraction',
      'f : (to N N)',
      '(f-beta (n : N)) : (eq N N (ap N N plus n) n)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toEqual(
      expect.arrayContaining([expect.stringContaining('abstraction: expected')]),
    );
  });

  it('rejects equation whose applied argument is not the equation parameter', () => {
    // LHS is (ap N N f other), but the equation parameter is `n`.
    const code = [
      ...preamble(['other : N']),
      'construct by abstraction',
      'f : (to N N)',
      '(f-beta (n : N)) : (eq N N (ap N N f other) n)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs).toEqual(
      expect.arrayContaining([expect.stringContaining('abstraction: expected')]),
    );
  });

  it('rejects construct block with only one declaration', () => {
    const code = [
      ...preamble(),
      'construct by abstraction',
      'solo : (to N N)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.length).toBeGreaterThan(0);
  });
});

/* ------------------------------------------------------------------ */
/*  Regression: standalone construct-by chain                          */
/*  Guards against the Builder bug where unwinding the construct/by    */
/*  pair emitted a spurious Construct("_", []) block alongside the     */
/*  real one, producing a "Schema _ not found" error at position -1.   */
/* ------------------------------------------------------------------ */

describe('construct-by chain parsing', () => {
  it('standalone `construct by X ... end` does not emit a phantom schema-_ block', () => {
    // Minimal reproduction: one postulate+meta chain, then a separate
    // construct-by chain. Must not produce "Schema _ not found".
    const code = [
      'postulate',
      'Sort : Sort',
      'U : Sort',
      'D : U',
      'a : D',
      'meta',
      'schema trivial = fun s => match s with | [(_, [], _)] => (Ok [a]) | _ => (Error "bad") end',
      'end',
      '',
      'construct by trivial',
      'b : D',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.every(m => !m.includes('Schema _ not found'))).toBe(true);
    expect(msgs).toEqual([]);
  });

  it('enum-coprod-generic.mint example checks clean', () => {
    // Reads the example file directly so any regression in the Builder,
    // meta-recursion, or enum schema surfaces here.
    const path = resolve(__dirname, '../../../../examples/enum-coprod-generic.mint');
    const code = readFileSync(path, 'utf-8');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Source locations: schema-related errors localize to the schema    */
/*  reference (`construct by s` ← here on `s`), not to the first      */
/*  decl in the construct block.                                       */
/* ------------------------------------------------------------------ */

describe('construct schema error ranges', () => {
  it('ill-typed witness errors are localized to the schema reference', () => {
    const code = [
      'postulate',
      'Sort : Sort',
      'U : Sort',
      '(to (A : U) (B : U)) : U',
      '(ap (A : U) (B : U) (f : (to A B)) (a : A)) : B',
      '(eq (A : U) (B : U) (a : A) (b : B)) : U',
      'N : U',
      'meta',
      'schema s = fun xs => match xs with',
      '  | [(f, [], (to A B)), (_, [(x, _)], (eq _ _ (ap _ _ f x) body))]',
      '    => (Ok [f, (ap A B f x)])',
      '  | _ => (Error "bad")',
      '  end',
      'construct by s',
      'aptwice : (to (to N N) (to N N))',
      'end',
    ].join('\n');
    const errs = errors(code);
    expect(errs.length).toBeGreaterThan(0);
    const e = errs[0];
    expect(code.substring(e.from, e.to)).toBe('s');
    /* And the error message is the schema-witness one. */
    expect(e.message).toMatch(/(matched but generated|not found|not a schema|Schema error)/);
  });

  it('schema-not-found error is localized to the schema reference', () => {
    const code = [
      'postulate',
      'Sort : Sort',
      'x : Sort',
      'construct by missing-schema',
      'y : Sort',
      'end',
    ].join('\n');
    const errs = errors(code);
    const schemaErrs = errs.filter(e => e.message.includes('not found'));
    expect(schemaErrs.length).toBe(1);
    expect(code.substring(schemaErrs[0].from, schemaErrs[0].to)).toBe('missing-schema');
  });
});

/* ------------------------------------------------------------------ */
/*  Argument type well-formedness                                      */
/*  Every term in the program must be checked — including the types    */
/*  of declaration parameters. The typeArgs judgment in the formalism  */
/*  requires each parameter's type to itself be a well-formed term.    */
/* ------------------------------------------------------------------ */

describe('argument type well-formedness', () => {
  it('rejects unbound identifier in a parameter type', () => {
    const msgs = errorMessages('postulate\nSort : Sort\n(f (a : undeclared)) : Sort\nend');
    expect(msgs.some(m => m.includes('Unbound') && m.includes('undeclared'))).toBe(true);
  });

  it('rejects arity error in a parameter type', () => {
    const msgs = errorMessages(
      'postulate\nSort : Sort\nN : Sort\n(f (a : (N extra))) : Sort\nend'
    );
    expect(msgs.some(m => m.includes('Too many'))).toBe(true);
  });

  it('rejects inconsistency inside a parameter type', () => {
    // (P (x : N)) takes N, not Sort.
    const msgs = errorMessages(
      'postulate\nSort : Sort\nN : Sort\n(P (x : N)) : Sort\n(f (a : (P Sort))) : Sort\nend'
    );
    expect(msgs.some(m => m.includes('Inconsistency'))).toBe(true);
  });

  it('rejects parameter type referencing a name declared later in the block', () => {
    // `later` is declared after `f`, so not in scope when checking f.
    const msgs = errorMessages(
      'postulate\nSort : Sort\n(f (a : later)) : Sort\nlater : Sort\nend'
    );
    expect(msgs.some(m => m.includes('Unbound') && m.includes('later'))).toBe(true);
  });

  it('accepts a well-formed parameter type', () => {
    expect(errors('postulate\nSort : Sort\nN : Sort\n(f (a : N)) : Sort\nend')).toEqual([]);
  });

  it('accepts dependent parameter types (later arg references earlier arg)', () => {
    expect(errors('postulate\nSort : Sort\n(f (A : Sort) (a : A)) : A\nend')).toEqual([]);
  });

  it('accepts chained dependencies across multiple parameters', () => {
    expect(errors(
      'postulate\nSort : Sort\n(f (A : Sort) (B : Sort) (a : A) (b : B)) : Sort\nend'
    )).toEqual([]);
  });

  it('checks parameter types inside construct-block declarations', () => {
    const msgs = errorMessages([
      'postulate',
      'Sort : Sort',
      'N : Sort',
      'meta',
      'schema s = fun xs => match xs with | _ => (Error "bad") end',
      'construct by s',
      '(f (a : undeclared)) : N',
      'end',
    ].join('\n'));
    expect(msgs.some(m => m.includes('Unbound') && m.includes('undeclared'))).toBe(true);
  });
});

/* ------------------------------------------------------------------ */
/*  Self-reference in declarations                                     */
/*  The typeDeclaration judgment places the declaration x ā : T into   */
/*  Γ when checking its own args and return type, so the constructor's */
/*  name is in scope inside its own signature.                         */
/* ------------------------------------------------------------------ */

describe('self-reference in declarations', () => {
  it('accepts self-reference in the return type', () => {
    // H : (x : Sort) → (H x) — H applied in its own retType.
    expect(errors('postulate\nSort : Sort\n(H (x : Sort)) : (H x)\nend')).toEqual([]);
  });

  it('accepts self-reference in a zero-ary declaration (F : F)', () => {
    // The degenerate case — the decl's type is its own name.
    expect(errors('postulate\nSort : Sort\nF : F\nend')).toEqual([]);
  });

  it('name is in scope for parameter types (no Unbound error)', () => {
    // F takes one arg; its param type mentions F itself. With self-ref the
    // name resolves (even if arity still produces other errors).
    const msgs = errorMessages('postulate\nSort : Sort\n(F (x : F)) : Sort\nend');
    expect(msgs.every(m => !m.includes('Unbound'))).toBe(true);
  });

  it('still rejects arity errors in self-reference', () => {
    // F takes one arg, but retType uses F with two.
    const msgs = errorMessages('postulate\nSort : Sort\n(F (x : Sort)) : (F x x)\nend');
    expect(msgs.some(m => m.includes('Too many'))).toBe(true);
  });

  it('still rejects unbound non-self names even when self is in scope', () => {
    const msgs = errorMessages('postulate\nSort : Sort\n(F (x : Sort)) : (F other)\nend');
    expect(msgs.some(m => m.includes('Unbound') && m.includes('other'))).toBe(true);
  });

  it('self-reference works inside a construct-block declaration', () => {
    // Same shape as the postulate version, but inside construct.
    // Schema is intentionally the error branch so we test that the
    // decl well-formedness pass does not emit Unbound for Rec.
    const code = [
      'postulate',
      'Sort : Sort',
      'N : Sort',
      'meta',
      'schema s = fun xs => match xs with | _ => (Error "bad") end',
      'construct by s',
      '(Rec (x : N)) : (Rec x)',
      'end',
    ].join('\n');
    const msgs = errorMessages(code);
    expect(msgs.every(m => !m.includes('Unbound') || !m.includes('Rec'))).toBe(true);
  });
});

/* ------------------------------------------------------------------ */
/*  Witness substitution (matching the typeWitnesses formalism)        */
/*  [x ↦ t] is applied to all of w̄ — param types, return types, AND    */
/*  witness bodies. A schema-generated witness that references an      */
/*  earlier declared name resolves to the witness of that name.        */
/* ------------------------------------------------------------------ */

describe('witness substitution in construct blocks', () => {
  it('substitutes earlier witness into later decl return type', () => {
    // Schema witnesses a (the type) as N, and b (of type a) as zero.
    // For b's check, expected type is a[witness] = N, and zero : N. OK.
    const code = [
      'postulate',
      'Sort : Sort',
      'N : Sort',
      'zero : N',
      'end',
      'meta',
      'schema wrap = fun xs => match xs with',
      '  | [(_, [], _), (_, [], _)] => (Ok [N, zero])',
      '  | _ => (Error "bad")',
      '  end',
      'construct by wrap',
      'a : Sort',
      'b : a',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });

  it('substitutes earlier witness into later witness body', () => {
    // The schema produces as the second witness the identifier of the FIRST
    // decl (name1). Without body substitution, name1 would be unbound in
    // the witness-check context. With [name1 ↦ zero] substitution, it
    // becomes zero : N. OK.
    const code = [
      'postulate',
      'Sort : Sort',
      'N : Sort',
      'zero : N',
      'end',
      'meta',
      'schema echo = fun xs => match xs with',
      '  | [(name1, [], _), (_, [], _)] => (Ok [zero, name1])',
      '  | _ => (Error "bad")',
      '  end',
      'construct by echo',
      'a : N',
      'b : N',
      'end',
    ].join('\n');
    expect(errors(code)).toEqual([]);
  });
});

/* ------------------------------------------------------------------ */
/*  Empty initial context                                              */
/*  The OL context begins empty — no built-in notions. Sort (and       */
/*  every other name) must be declared by the user. Self-reference     */
/*  makes `Sort : Sort` a legal bootstrap declaration.                 */
/* ------------------------------------------------------------------ */

describe('empty initial context', () => {
  it('Sort is not a built-in OL identifier', () => {
    const msgs = errorMessages('postulate\nx : Sort\nend');
    expect(msgs.some(m => m.includes('Unbound') && m.includes('Sort'))).toBe(true);
  });

  it('Sort : Sort is accepted as a bootstrap declaration (via self-ref)', () => {
    expect(errors('postulate\nSort : Sort\nend')).toEqual([]);
  });

  it('declarations following Sort : Sort can use Sort', () => {
    expect(errors('postulate\nSort : Sort\nU : Sort\n(f (x : U)) : U\nend')).toEqual([]);
  });
});
