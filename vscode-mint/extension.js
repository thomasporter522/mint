/* Mint VS Code extension.

   Runs `mintc <file>` on file open + (save or change, configurable),
   parses its output for diagnostic lines, and surfaces them as VS Code
   `Diagnostic`s. Two formats are recognized:

     1. mintc's own:   `path:line:col: <kind>: <message>`
            kind ∈ {error, warning, hole}
     2. OCaml's:       `File "path", line N, characters X-Y:`
                       followed by an `Error: ...` line (or several)

   This is the spike-shape integration: nothing more elaborate than
   shelling out and pattern-matching stdout. A real LSP server is the
   natural follow-up if richer affordances (hover, go-to-def, inlay
   hints) are wanted. */

const vscode = require('vscode')
const cp = require('child_process')
const path = require('path')
const fs = require('fs')

let diagnostics
let outputChannel
let pendingTimers = new Map() // doc URI string → NodeJS.Timer (debounce)
// Per-doc hole goals shown via the HoverProvider. Holes never become
// Diagnostics — no squiggle, no Problems-panel entry.
const holesByDoc = new Map() // doc URI string → Array<{ range, goal }>
// Per-doc inlay hints emitted by the kernel: implicit-arg insertions
// at constructor sites (rendered as `…`) and coercion wrappings
// (rendered as `°`, once the kernel actually emits them).
const hintsByDoc = new Map() // doc URI string → Array<{ position, kind, tooltip }>
const hintsChanged = new vscode.EventEmitter()

function activate(context) {
  diagnostics = vscode.languages.createDiagnosticCollection('mint')
  outputChannel = vscode.window.createOutputChannel('Mint')
  context.subscriptions.push(diagnostics, outputChannel)

  // Initial pass for already-open docs (e.g., when reloading the window).
  for (const doc of vscode.workspace.textDocuments) refresh(doc)

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(refresh),
    vscode.workspace.onDidSaveTextDocument(refresh),
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (runOnChange()) scheduleRefresh(e.document)
    }),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      diagnostics.delete(doc.uri)
      const id = doc.uri.toString()
      const t = pendingTimers.get(id)
      if (t) { clearTimeout(t); pendingTimers.delete(id) }
      holesByDoc.delete(id)
      hintsByDoc.delete(id)
    })
  )

  context.subscriptions.push(
    vscode.languages.registerInlayHintsProvider('mint', {
      onDidChangeInlayHints: hintsChanged.event,
      provideInlayHints(document, range) {
        const all = hintsByDoc.get(document.uri.toString()) || []
        const out = []
        for (const h of all) {
          if (!range.contains(h.position)) continue
          const label = h.kind === 'coerce' ? '°' : '…'
          const hint = new vscode.InlayHint(h.position, label)
          hint.tooltip = new vscode.MarkdownString(`\`${h.tooltip}\``)
          hint.paddingLeft = true
          out.push(hint)
        }
        return out
      }
    })
  )

  // Hover-only display for hole goals. The kernel reports each `?`'s
  // inferred type; we surface it only when the user hovers, so the
  // source itself stays unadorned.
  context.subscriptions.push(
    vscode.languages.registerHoverProvider('mint', {
      provideHover(document, position) {
        const holes = holesByDoc.get(document.uri.toString()) || []
        for (const h of holes) {
          if (h.range.contains(position)) {
            return new vscode.Hover(`: ${h.goal}`, h.range)
          }
        }
        return null
      }
    })
  )
}

function deactivate() {}

function runOnChange() {
  return vscode.workspace.getConfiguration('mint').get('runOn') === 'change'
}

function scheduleRefresh(doc) {
  const id = doc.uri.toString()
  const prev = pendingTimers.get(id)
  if (prev) clearTimeout(prev)
  pendingTimers.set(id, setTimeout(() => {
    pendingTimers.delete(id)
    refresh(doc)
  }, 250))
}

function findMintc() {
  const config = vscode.workspace.getConfiguration('mint')
  let p = config.get('mintcPath')
  if (p && p.trim()) return p.trim()

  const folders = vscode.workspace.workspaceFolders
  if (folders && folders.length > 0) {
    const candidate = path.join(
      folders[0].uri.fsPath,
      '_build', 'default', 'src', 'mintc.bc.exe'
    )
    if (fs.existsSync(candidate)) return candidate
  }
  return null
}

function refresh(doc) {
  if (doc.languageId !== 'mint') return

  const mintc = findMintc()
  if (!mintc) {
    outputChannel.appendLine(
      '[mint] mintc binary not found. Set "mint.mintcPath" or `make build` ' +
      'in the workspace root.'
    )
    return
  }

  // If running on-change, we feed the current buffer via a temp file
  // (so unsaved edits get analyzed). Otherwise we point mintc at the
  // saved on-disk path directly.
  let target = doc.uri.fsPath
  let cleanup = null
  if (runOnChange() && doc.isDirty) {
    const tmpdir = require('os').tmpdir()
    const tmp = path.join(
      tmpdir,
      `mint-${process.pid}-${Date.now()}-${path.basename(doc.uri.fsPath)}`
    )
    fs.writeFileSync(tmp, doc.getText())
    target = tmp
    cleanup = () => { try { fs.unlinkSync(tmp) } catch (_) {} }
  }

  cp.execFile(
    mintc, [target],
    { timeout: 10000, maxBuffer: 4 * 1024 * 1024 },
    (_err, stdout, stderr) => {
      if (cleanup) cleanup()
      const out = (stdout || '') + (stderr || '')
      const { items, holes, hints } = parseOutput(out, doc, target)
      diagnostics.set(doc.uri, items)
      holesByDoc.set(doc.uri.toString(), holes)
      hintsByDoc.set(doc.uri.toString(), hints)
      hintsChanged.fire()
    }
  )
}

/* Diagnostic patterns. */
const OWN_LINE = /^(.+?):(\d+):(\d+): (error|warning|hole): (.+)$/
const HINT_LINE = /^(.+?):(\d+):(\d+): hint (implicit|coerce): (.+)$/
const OCAML_HEADER = /^File "(.+?)", line (\d+), characters (\d+)-(\d+):\s*$/

function parseOutput(output, doc, sourcePath) {
  const items = []
  const holes = []
  const hints = []
  const lines = output.split('\n')
  const sourceBase = path.basename(sourcePath)

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]

    const mh = line.match(HINT_LINE)
    if (mh) {
      const [, fpath, lineStr, colStr, kind, tooltip] = mh
      if (path.basename(fpath) !== sourceBase) continue
      const ln = parseInt(lineStr, 10) - 1
      const col = parseInt(colStr, 10) - 1
      hints.push({
        position: new vscode.Position(ln, col),
        kind,
        tooltip,
      })
      continue
    }

    const m1 = line.match(OWN_LINE)
    if (m1) {
      const [, fpath, lineStr, colStr, kind, msg] = m1
      if (path.basename(fpath) !== sourceBase) continue
      const ln = parseInt(lineStr, 10) - 1
      const col = parseInt(colStr, 10) - 1
      const range = widenToIdentifier(doc, ln, col)

      if (kind === 'hole') {
        // mintc emits `goal = TYPE`; strip the prefix for the hover.
        const g = msg.match(/^goal\s*=\s*(.+)$/)
        holes.push({ range, goal: g ? g[1] : msg })
      } else {
        items.push(diag(range, msg, severityOf(kind)))
      }
      continue
    }

    const m2 = line.match(OCAML_HEADER)
    if (m2) {
      const [, fpath, lineStr, fromStr, toStr] = m2
      if (path.basename(fpath) !== sourceBase) continue
      const ln = parseInt(lineStr, 10) - 1
      const fromCol = parseInt(fromStr, 10)
      const toCol = parseInt(toStr, 10)
      // Next non-blank line(s) (up to 5) are the error body. Stop at a
      // blank line, another `File "..."` header, or our own format.
      let msg = ''
      for (let j = i + 1; j < lines.length && j < i + 6; j++) {
        const next = lines[j]
        if (next.trim() === '') break
        if (OCAML_HEADER.test(next) || OWN_LINE.test(next)) break
        msg += (msg ? ' ' : '') + next.trim()
      }
      const range = new vscode.Range(ln, fromCol, ln, toCol)
      items.push(diag(range, msg || 'OCaml error', vscode.DiagnosticSeverity.Error))
    }
  }

  return { items, holes, hints }
}

function severityOf(kind) {
  switch (kind) {
    case 'error':   return vscode.DiagnosticSeverity.Error
    case 'warning': return vscode.DiagnosticSeverity.Warning
    default:        return vscode.DiagnosticSeverity.Hint
  }
}

function diag(range, message, severity) {
  const d = new vscode.Diagnostic(range, message, severity)
  d.source = 'mint'
  return d
}

/* The kernel reports a single point. Widen forward to cover the
   identifier (or `?` hole) starting at that point — better-looking
   squiggle than a single character. */
function widenToIdentifier(doc, ln, col) {
  try {
    const line = doc.lineAt(ln).text
    let end = col
    while (end < line.length && /[A-Za-z0-9_\-?]/.test(line[end])) end++
    if (end === col) end = col + 1
    return new vscode.Range(ln, col, ln, end)
  } catch (_) {
    return new vscode.Range(ln, col, ln, col + 1)
  }
}

module.exports = { activate, deactivate }
