import { describe, it, expect } from 'vitest';
import { processCode, parseAndPrint } from '../reason-bridge';

function check(code: string) {
  return processCode(code) as any;
}

describe('destructuring let', () => {
  it('tuple pattern binds both components', () => {
    // Use the destructuring in a meta procedure that's exercised by a
    // construct block, since meta let-bodies need a top-level driver.
    const code = `postulate
U : U
foo : U
bar : U
meta
  schema s = fun ctx => fun args =>
    let (a, b) = (foo, bar) in
    (Ok [a, b])
construct by s
x : U
y : U
`;
    const r = check(code);
    expect(r.errors.filter((e: any) => e.type === 'mark')).toEqual([]);
  });

  it('nested tuple pattern', () => {
    const code = `postulate
U : U
foo : U
bar : U
baz : U
meta
  schema s = fun ctx => fun args =>
    let ((a, b), c) = ((foo, bar), baz) in
    (Ok [a, b, c])
construct by s
x : U
y : U
z : U
`;
    const r = check(code);
    expect(r.errors.filter((e: any) => e.type === 'mark')).toEqual([]);
  });

  it('simple name still works (PVar pattern)', () => {
    const code = `postulate
U : U
foo : U
meta
  schema s = fun ctx => fun args =>
    let x = foo in
    (Ok [x])
construct by s
y : U
`;
    const r = check(code);
    expect(r.errors.filter((e: any) => e.type === 'mark')).toEqual([]);
  });

  it('printer round-trips a destructuring let', () => {
    const code = `meta\nfoo = let (a, b) = (x, y) in a\n`;
    const out = parseAndPrint(code);
    // Both `a` and `b` should appear in the printed form, with the tuple pattern intact.
    expect(out).toContain('let (a, b) =');
    expect(out).toContain('(x, y)');
  });

  it('Cons pattern destructures lists', () => {
    const code = `postulate
U : U
foo : U
meta
  schema s = fun ctx => fun args =>
    let h :: t = [foo] in
    (Ok [h])
construct by s
y : U
`;
    const r = check(code);
    expect(r.errors.filter((e: any) => e.type === 'mark')).toEqual([]);
  });
});
