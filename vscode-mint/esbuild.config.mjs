/* Bundle the extension into a single CJS file the VS Code extension host
   loads. `vscode` is provided by the host and must be marked external. */

import { build } from 'esbuild'

await build({
  entryPoints: ['src/extension.ts'],
  bundle: true,
  outfile: 'dist/extension.js',
  external: ['vscode'],
  format: 'cjs',
  platform: 'node',
  target: 'node18',
  sourcemap: true,
  logLevel: 'info',
})
