import { describe, it } from 'vitest';
import { readFileSync } from 'fs';
import { resolve } from 'path';
import { processCode } from '../reason-bridge';

describe('strip debug', () => {
  it('runs fun.mint', () => {
    const code = readFileSync(resolve(__dirname, '../../../../examples/fun.mint'), 'utf-8');
    processCode(code);
  });
});
