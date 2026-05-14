import * as vscode from 'vscode'
// The engine lives at web/src/frontend/reason-bridge.ts so the web app, the
// CLI, and this extension all use the same canonical processCode.
// Esbuild bundles it (along with the Lezer parser and the Melange-compiled
// OCaml output) into dist/extension.js at build time.
import { processCode, printTerm } from '../../web/src/frontend/reason-bridge'

const MINT_LANGUAGE = 'mint'

let diagnostics: vscode.DiagnosticCollection

// Per-doc raw inlay-hint data from the engine: (offset, label, tooltip).
// `offset` is the position immediately AFTER the term former's last
// character. Surfaced as `InlayHint`s — the engine-provided offset is
// already pinned to the identifier's natural end (the builder lifts
// paren-wrapped identifiers to OLAp(_, []) so the head retains its
// natural source range), so the hint renders right next to the head
// even when there's whitespace before the next arg. Using InlayHint
// (rather than a TextEditorDecoration with `after.contentText`) means
// the engine-provided tooltip fires when the user hovers the
// ellipsis itself, not just over the source character beside it.
const inlayHintsByDoc = new Map<string, [number, string, string][]>()
const inlayHintsChanged = new vscode.EventEmitter<void>()

// Per-doc definition records: (useFrom, useTo, defFrom, defTo). Read by
// the DefinitionProvider on ctrl-click / Go-to-Definition.
const definitionsByDoc = new Map<string, [number, number, number, number][]>()

// Decoration type used to put a small green ✓ before each complete block's
// keyword (`postulate` / `construct`). A block is complete when every decl
// in it has a hole-free type and witness, no errors anywhere in the block's
// range, and all transitively-referenced decls are themselves complete.
// Created once at activation; applied via setDecorations after each check.
let completeDecorationType: vscode.TextEditorDecorationType
const completeBlocksByDoc = new Map<string, [number, number][]>()

export function activate(context: vscode.ExtensionContext): void {
  diagnostics = vscode.languages.createDiagnosticCollection(MINT_LANGUAGE)
  context.subscriptions.push(diagnostics)

  completeDecorationType = vscode.window.createTextEditorDecorationType({
    before: {
      contentText: '✓',
      color: new vscode.ThemeColor('charts.green'),
      margin: '0 0.3em 0 0',
    },
  })
  context.subscriptions.push(completeDecorationType)

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(refresh),
    vscode.workspace.onDidChangeTextDocument((e) => refresh(e.document)),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      diagnostics.delete(doc.uri)
      inlayHintsByDoc.delete(doc.uri.toString())
      definitionsByDoc.delete(doc.uri.toString())
      completeBlocksByDoc.delete(doc.uri.toString())
    }),
    /* Re-apply decorations when an editor becomes visible (e.g. user
       switches tabs) — TextEditorDecorationType state is per-editor. */
    vscode.window.onDidChangeVisibleTextEditors(applyCompleteDecorations),
  )

  context.subscriptions.push(
    vscode.languages.registerInlayHintsProvider(MINT_LANGUAGE, {
      onDidChangeInlayHints: inlayHintsChanged.event,
      provideInlayHints(document, range) {
        const hints = inlayHintsByDoc.get(document.uri.toString()) ?? []
        const result: vscode.InlayHint[] = []
        for (const [offset, label, tooltip] of hints) {
          const pos = document.positionAt(offset)
          if (!range.contains(pos)) continue
          const hint = new vscode.InlayHint(pos, label)
          const ch = document.getText().charAt(offset)
          const prevCh = offset > 0 ? document.getText().charAt(offset - 1) : ''
          const isWS = (c: string) => c === ' ' || c === '\t' || c === '\n' || c === ''
          /* Implicit-args (`…`) hints are SUFFIX-anchored: positioned at
             `f.meta.end_`, just past the term former. They want padding
             between themselves and what follows. Coerce (`˚`) hints are
             PREFIX-anchored: positioned right before the coerced subject,
             hugging it. They want no right-padding (so they sit against
             the subject) and left-padding when something non-whitespace
             precedes them. */
          const isCoerce = label === '˚'
          if (isCoerce) {
            hint.paddingLeft = !isWS(prevCh)
            hint.paddingRight = false
          } else {
            hint.paddingRight = !isWS(ch)
          }
          hint.tooltip = tooltip
          result.push(hint)
        }
        return result
      },
    }),
  )

  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(MINT_LANGUAGE, {
      provideDefinition(document, position) {
        const offset = document.offsetAt(position)
        const defs = definitionsByDoc.get(document.uri.toString()) ?? []
        // Prefer the smallest (most specific) enclosing record, since
        // identifier-level uses can be nested inside larger ranges.
        let best: [number, number, number, number] | null = null
        for (const rec of defs) {
          const [useFrom, useTo] = rec
          if (offset < useFrom || offset >= useTo) continue
          if (!best || useTo - useFrom < best[1] - best[0]) best = rec
        }
        if (!best) return null
        const [useFrom, useTo, defFrom, defTo] = best
        const targetRange = rangeFromOffsets(document, defFrom, defTo)
        const link: vscode.LocationLink = {
          targetUri: document.uri,
          targetRange,
          /* Selecting the name on navigation makes the post-jump highlight
           * use the cursor-selection color rather than VS Code's range-
           * highlight color (the orange flash). */
          targetSelectionRange: targetRange,
          originSelectionRange: rangeFromOffsets(document, useFrom, useTo),
        }
        return [link]
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
    definitionsByDoc.set(document.uri.toString(), [])
    completeBlocksByDoc.set(document.uri.toString(), [])
    inlayHintsChanged.fire()
    applyCompleteDecorations(vscode.window.visibleTextEditors)
    return
  }

  const items: vscode.Diagnostic[] = []

  for (const err of result.errors) {
    const severity =
      err.type === 'warning'
        ? vscode.DiagnosticSeverity.Warning
        : vscode.DiagnosticSeverity.Error
    const diag = new vscode.Diagnostic(
      rangeFromOffsets(document, err.from, err.to),
      err.message,
      severity,
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
  definitionsByDoc.set(document.uri.toString(), result.definitions)
  completeBlocksByDoc.set(document.uri.toString(), result.completeBlocks)
  inlayHintsChanged.fire()
  applyCompleteDecorations(vscode.window.visibleTextEditors)
}

/* Apply (or refresh) the ✓ decorations on every visible editor that's
   showing a Mint document we have completeness data for. */
function applyCompleteDecorations(
  editors: readonly vscode.TextEditor[],
): void {
  for (const editor of editors) {
    if (editor.document.languageId !== MINT_LANGUAGE) continue
    const ranges = completeBlocksByDoc.get(editor.document.uri.toString()) ?? []
    editor.setDecorations(
      completeDecorationType,
      ranges.map(([from, to]) => rangeFromOffsets(editor.document, from, to)),
    )
  }
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
