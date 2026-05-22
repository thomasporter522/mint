import { describe, it, expect } from 'vitest';
import { processCode } from '../reason-bridge';

function noSyntaxErrors(code: string) {
  const r: any = processCode(code);
  const syntactic = r.errors.filter((e: any) => e.type === 'syntax');
  return syntactic;
}

describe('no parens needed around juxtaposition in delimited positions', () => {
  it("user's example 1: `let t1r = head-reduce t1 in …`", () => {
    const code = `meta\nf = let t1r = head-reduce t1 in t1r\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });

  it("user's example 2: `match beta-convert ctx expected found with …`", () => {
    const code = `meta\nf = match beta-convert ctx expected found with | _ => x end\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });

  it('let-RHS: `let t = foo bar in t`', () => {
    const code = `meta\nf = let t = foo bar in t\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });

  // Note: let-body and fun-body do NOT relax — they have only an opening
  // delimiter (`in` / `=>`) and no closing one, so juxtaposition there
  // would let the body run into the next meta-let item. Both still
  // require parens around any juxtaposition app inside them.

  it('match scrut: `match foo bar baz with | _ => x end`', () => {
    const code = `meta\nf = match foo bar baz with | _ => x end\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });

  it('match arm body: `| _ => foo bar`', () => {
    const code = `meta\nf = match s with | _ => foo bar end\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });

  it('if branches', () => {
    const code = `meta\nf = if c then foo bar else baz qux end\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });


  it('meta-let RHS is unchanged (no juxtaposition there to keep block items distinguishable)', () => {
    // `foo = bar baz qux = next` would be ambiguous if we relaxed
    // meta-let RHS to allow juxtaposition. Test that the existing
    // single-name behavior still works.
    const code = `meta\nfoo = bar\nqux = baz\n`;
    expect(noSyntaxErrors(code)).toEqual([]);
  });
});
