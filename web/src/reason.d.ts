declare module '@reason/Lytr_api.js' {
  export function processCode(code: string): {
    errors: Array<{ type: string; message: string; from: number; to: number }>;
    holes: Array<[number, { goal: any; context: Map<string, any> }]>;
  };
  export function printTerm(term: any): string;
  export function parseAndPrint(code: string): string;
  export function parseAndDebug(code: string): string;
  export function lexToTokens(code: string): number[];
  export function checkSchemaCode(code: string): { ok: boolean; error: string; from: number; to: number };
}
