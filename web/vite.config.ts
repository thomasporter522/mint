import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import path from 'path'

const melangeOutput = path.resolve(__dirname, '../reason/_build/default/src/output')

// https://vite.dev/config/
export default defineConfig({
  plugins: [react()],
  resolve: {
    alias: {
      'melange.js': path.join(melangeOutput, 'node_modules/melange.js'),
      'melange': path.join(melangeOutput, 'node_modules/melange'),
      '@reason': path.join(melangeOutput, 'src'),
    },
  },
})
