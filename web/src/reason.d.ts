declare module '@reason/Lytr_api.js' {
  /* New AST-based entry points. The TS builder produces values matching
     web/src/lytr/ast.ts and these are decoded by reason/src/Decode.re. */
  export function processProgramJs(jsArr: unknown[]): {
    errors: Array<{ type: string; message: string; from: number; to: number }>;
    holes: Array<[number, { goal: any; context: Map<string, any> }]>;
  };
  export function printProgramJs(jsArr: unknown[]): string;
  export function printMLJs(jsML: unknown): string;
  export function checkSchemaMLJs(jsML: unknown): { ok: boolean; error: string; from: number; to: number };
  export function evalMLJs(jsML: unknown): { ok: boolean; value: string; error: string };

  /* Print a single OCaml-side term value (opaque to TS). */
  export function printTerm(term: any): string;
}
