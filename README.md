# The Mint Proof System

Mint's design is centered around the virtue of *objectivity*: the semantics
should be easily read off of the syntax, with as little semantic obfuscation
and variation as possible. The object-level language is built from
dependently typed term formers. Every term former must be postulated or
constructed; none are built in.

The meta language — what runs inside `meta { … }` blocks and what schemas
and coerce procedures are written in — is OCaml (or Reason via
[`refmt`](https://reasonml.github.io/)). The kernel hands meta-block source
to a long-lived in-process Toploop session built on `compiler-libs.toplevel`,
extends OCaml's type system with the user's postulated constructors as
extensible-variant arms, and lets meta code call directly into the resulting
types. The `Mint` kernel-bridge module exposes the affordances meta code
needs (`signature`, `hole`, `is_hole`, `canonical`, …).

## Getting Started

```
make build                          # builds mintc.bc.exe
make run FILE=examples/basic.mint   # one example
make test                           # every example
```

Requires a recent OCaml + dune. To use Reason syntax in `meta` blocks,
`refmt` must be on `PATH` (it's part of any standard
[Reason](https://reasonml.github.io/) install).

## VS Code extension

```
make vscode-install        # symlinks vscode-mint/ into ~/.vscode/extensions
                           # then reload VS Code (Cmd-Shift-P → Developer: Reload Window)
make vscode-uninstall
```

The extension activates on `.mint` files. On open + save (or on every
keystroke if you set `mint.runOn: change`), it shells out to `mintc`
and parses the diagnostic lines back into VS Code `Diagnostic`s.
Errors and OCaml type errors surface as red squiggles; holes surface
as Information-severity items in the Problems panel (showing the
inferred goal type).

Settings:
- `mint.mintcPath` — absolute path to `mintc.bc.exe`. Defaults to
  `<workspace>/_build/default/src/mintc.bc.exe`.
- `mint.runOn` — `"save"` (default) or `"change"`.

## Layout

```
mint/
├── dune-project
├── Makefile
├── README.md
├── src/                 ; OCaml kernel
│   ├── dune             ;   toplevel executable: `mintc.bc.exe`
│   ├── ast.ml           ;   OL AST: ol_decl / decl_line / block / program
│   ├── lexer.ml         ;   token stream for decl lines
│   ├── parser.ml        ;   block-level + decl + tag-line parser
│   │                    ;     - indentation-based multi-line continuation
│   ├── check.ml         ;   OL elaboration:
│   │                    ;     - meta management (mkMeta / follow / zonk / occurs)
│   │                    ;     - unification, resolve
│   │                    ;     - typeDeclaration rule (self-binding, zonk-and-forget)
│   ├── translator.ml    ;   AST → OCaml top-level phrases
│   │                    ;     - `type term += ...` per postulate/construct
│   │                    ;     - `Mint` kernel-bridge module
│   │                    ;     - `#line` directives so OCaml errors map to .mint lines
│   │                    ;     - refmt shell-out for Reason syntax in meta blocks
│   ├── driver.ml        ;   long-lived Toploop session
│   ├── error.ml         ;   diagnostics (`mark`/`warn`, line_col, pp)
│   └── mintc.ml         ;   CLI entry point
├── examples/            ; .mint files
│   ├── basic.mint
│   ├── tagged.mint
│   ├── multiline.mint
│   ├── reason-syntax.mint
│   ├── bridge.mint
│   ├── holes.mint
│   ├── errors-ol.mint
│   └── errors-ocaml.mint
├── vscode-mint/         ; VS Code extension; shells out to mintc
└── vendor/Canonical/    ; canonical solver (git submodule)
```

## Pipeline

```
.mint source
  │
  ▼
parser.ml  ──▶  AST  (postulate / meta / construct blocks)
  │
  ▼
check.ml   ──▶  static_info { errors; holes; bindings }
  │
  ▼  (only if no real errors)
translator.ml ──▶ ordered list of OCaml top-level phrases
  │
  ▼
driver.ml  ──▶  Toploop session
              (type extensions + value bindings persist;
               construct blocks synthesize a kernel-side
               invocation of the named schema and print its
               witnesses)
```

## Examples

| File                         | Demonstrates                                                |
|------------------------------|-------------------------------------------------------------|
| `examples/basic.mint`        | postulate + meta + construct, schema returns witnesses      |
| `examples/tagged.mint`       | `#tag` lines threaded into a signature's `tags`             |
| `examples/multiline.mint`    | indent-based multi-line decl continuation                   |
| `examples/reason-syntax.mint`| meta block in Reason syntax (refmt-converted)               |
| `examples/bridge.mint`       | `Mint.hole`, `Mint.is_hole`, mixed-witness schema           |
| `examples/holes.mint`        | OL `?` holes, kernel reports each goal's inferred type      |
| `examples/errors-ol.mint`    | unbound-identifier diagnostics with `file:line:col`         |
| `examples/errors-ocaml.mint` | OCaml errors mapped back to original Mint source lines      |

## Future directions

- Wire `Mint.canonical` to the vendored Canonical solver via shell-out.
- Per-constructor printer registry so the kernel can render any term
  without the user supplying `string_of_term`.
- Inlay-hint extraction (the data is already in `static_info`).
- User-defined syntax (unicode, mixfix).
- A module-like system for reusable, nested hypothetical reasoning.
- IDE integration (LSP, VS Code extension) talking to `mintc` over stdin/stdout.
