import { describe, it } from 'vitest';
import { readFileSync } from 'fs';
import { resolve } from 'path';
import { processCode } from '../reason-bridge';

function check(file: string) {
  const code = readFileSync(resolve(__dirname, '../../../../examples', file), 'utf-8');
  const r: any = processCode(code);
  return { code, ...r };
}

describe('fun-convert', () => {
  it('processes fun-convert.mint without crashing', () => {
    const r = check('fun-convert.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
    const coerceHints = (r.inlayHints ?? []).filter((h: any) => {
      const label = h[1];
      return label && label.includes('˚');
    });
    if (coerceHints.length > 0) console.log(`coerce hints (˚): ${coerceHints.length}`);
  }, 60000);

  it('processes test-convert-simple.mint', () => {
    const r = check('test-convert-simple.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
    const coerceHints = (r.inlayHints ?? []).filter((h: any) => {
      const label = h[1];
      return label && label.includes('˚');
    });
    if (coerceHints.length > 0) console.log(`coerce hints (˚): ${coerceHints.length}`);
  });

  it('processes test-convert-cong.mint', () => {
    const r = check('test-convert-cong.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
    const coerceHints = (r.inlayHints ?? []).filter((h: any) => {
      const label = h[1];
      return label && label.includes('˚');
    });
    if (coerceHints.length > 0) console.log(`coerce hints (˚): ${coerceHints.length}`);
  });

  it('processes test-convert-deep.mint', () => {
    const r = check('test-convert-deep.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
    const coerceHints = (r.inlayHints ?? []).filter((h: any) => {
      const label = h[1];
      return label && label.includes('˚');
    });
    if (coerceHints.length > 0) console.log(`coerce hints (˚): ${coerceHints.length}`);
  });

  it('processes test-convert-mixed.mint', () => {
    const r = check('test-convert-mixed.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
  });

  it('processes test-convert-chain.mint', () => {
    const r = check('test-convert-chain.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
  });

  it('processes test-convert-eq.mint', () => {
    const r = check('test-convert-eq.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
  });

  it('processes test-convert-sap.mint', () => {
    const r = check('test-convert-sap.mint');
    console.log(`errors: ${r.errors.length}`);
    for (const e of r.errors.slice(0, 10)) {
      console.log(`  ${e.from}-${e.to} [${e.type}]: ${e.message?.slice(0, 200)}`);
    }
    const coerceHints = (r.inlayHints ?? []).filter((h: any) => {
      const label = h[1];
      return label && label.includes('˚');
    });
    if (coerceHints.length > 0) console.log(`coerce hints (˚): ${coerceHints.length}`);
  });

  it('test-convert-fail.mint: coerce correctly fails on unrelated types', () => {
    const r = check('test-convert-fail.mint');
    const marks = r.errors.filter((e: any) => e.type === 'mark');
    console.log(`mark errors: ${marks.length}`);
    for (const e of marks) {
      console.log(`  ${e.from}-${e.to}: ${e.message?.slice(0, 200)}`);
    }
    // Expect at least one mark error: the bad : Q decl.
    if (marks.length === 0) throw new Error('expected coerce to fail on P vs Q');
  });
});
