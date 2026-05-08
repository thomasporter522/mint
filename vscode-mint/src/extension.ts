import * as vscode from 'vscode'
// The engine lives at web/src/lytr/reason-bridge.ts so the web app, the
// CLI, and this extension all use the same canonical processCode.
// Esbuild bundles it (along with the Lezer parser and the Melange-compiled
// OCaml output) into dist/extension.js at build time.
import { processCode, printTerm } from '../../web/src/lytr/reason-bridge'

const MINT_LANGUAGE = 'mint'

let diagnostics: vscode.DiagnosticCollection

// Latest inlay hints per document URI, populated by refresh() and read by
// the InlayHintsProvider. Each entry is (offset, content): render `content`
// (a printed form of one or more ghost subterms) anchored just before `offset`.
const inlayHintsByDoc = new Map<string, [number, string][]>()
const inlayHintsChanged = new vscode.EventEmitter<void>()

export function activate(context: vscode.ExtensionContext): void {
  diagnostics = vscode.languages.createDiagnosticCollection(MINT_LANGUAGE)
  context.subscriptions.push(diagnostics)

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(refresh),
    vscode.workspace.onDidChangeTextDocument((e) => refresh(e.document)),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      diagnostics.delete(doc.uri)
      inlayHintsByDoc.delete(doc.uri.toString())
    }),
  )

  context.subscriptions.push(
    vscode.languages.registerInlayHintsProvider(MINT_LANGUAGE, {
      onDidChangeInlayHints: inlayHintsChanged.event,
      provideInlayHints(document, range) {
        const hints = inlayHintsByDoc.get(document.uri.toString()) ?? []
        const result: vscode.InlayHint[] = []
        for (const [offset, content] of hints) {
          const pos = document.positionAt(offset)
          if (!range.contains(pos)) continue
          const hint = new vscode.InlayHint(pos, content)
          hint.paddingRight = true
          result.push(hint)
        }
        return result
      },
    }),
  )

  // Cover any Mint files already open at activation.
  vscode.workspace.textDocuments.forEach(refresh)
}

export function deactivate(): void {
  diagnostics?.dispose()
  inlayHintsChanged.dispose()
}

function refresh(document: vscode.TextDocument): void {
  if (document.languageId !== MINT_LANGUAGE) return

  const code = document.getText()
  let result: ReturnType<typeof processCode>
  try {
    result = processCode(code)
  } catch (e) {
    // The engine is not supposed to throw; if it does, surface it
    // visibly rather than silently dropping diagnostics.
    diagnostics.set(document.uri, [
      new vscode.Diagnostic(
        new vscode.Range(0, 0, 0, 1),
        `Mint engine error: ${(e as Error).message}`,
        vscode.DiagnosticSeverity.Error,
      ),
    ])
    inlayHintsByDoc.set(document.uri.toString(), [])
    inlayHintsChanged.fire()
    return
  }

  const items: vscode.Diagnostic[] = []

  for (const err of result.errors) {
    const diag = new vscode.Diagnostic(
      rangeFromOffsets(document, err.from, err.to),
      err.message,
      vscode.DiagnosticSeverity.Error,
    )
    diag.source = err.type
    items.push(diag)
  }

  for (const [pos, info] of result.holes) {
    const goal = printTerm(info.goal)
    const diag = new vscode.Diagnostic(
      rangeFromOffsets(document, pos, pos + 1),
      `? : ${goal}`,
      vscode.DiagnosticSeverity.Hint,
    )
    diag.source = 'hole'
    items.push(diag)
  }

  diagnostics.set(document.uri, items)
  inlayHintsByDoc.set(document.uri.toString(), result.inlayHints)
  inlayHintsChanged.fire()
}

function rangeFromOffsets(
  doc: vscode.TextDocument,
  from: number,
  to: number,
): vscode.Range {
  const safeFrom = from < 0 ? 0 : Math.min(from, doc.getText().length)
  const safeTo = to <= from ? safeFrom + 1 : Math.min(to, doc.getText().length)
  return new vscode.Range(doc.positionAt(safeFrom), doc.positionAt(safeTo))
}
