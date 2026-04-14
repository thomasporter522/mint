# Assignment 5: Builder

## Overview

The builder converts the parser's `openForm` tree into the `Term.re` AST. It is
a recursive descent over the parse tree, dispatching on the structure of each
form to produce the corresponding AST node.

`Parser.re` (previous assignment) produces a list of `sharded(openForm)` values.
Your job is to fill in `Builder.re` so that every parse tree shape maps to the
correct `cTerm` variant.

## File to implement

- **Builder.re** -- parse tree to AST

## The openForm structure

After the parser's operatorize phase, every primary token lives inside an
`openForm`:

```
openForm = {
  left:    option(openForm),   (* left child -- higher-precedence subtree *)
  leftUf:  list(unform),       (* unforms between left child and token *)
  closed:  closedForm,         (* the token itself, possibly with matched interior *)
  rightUf: list(unform),       (* unforms between token and right child *)
  right:   option(openForm),   (* right child -- higher-precedence subtree *)
}
```

A `closedForm` is either a bare token (`CHead(tok)`) or a matched pair with
interior items (`CMatch(inner, items, closingTok)`). Matched pairs nest: a
`match...with...|...=>...end` chain is a deeply nested `CMatch` tree.

## How buildForm dispatches

`buildForm` is the main function. It pattern-matches on the five fields of an
`openForm` simultaneously. The dispatch order matters -- earlier cases take
priority.

### 1. Bracket forms

Pattern: no left/right child, closed form ends with `)` or `]`.

The builder walks the nested `CMatch` structure via `collectBracketElements` to
gather comma-separated groups. Then:

- **Parentheses `(...)`**: a single element becomes a parenthesized term (the
  `parens` flag is set on its metadata). Multiple elements become nested `Comma`
  nodes.
- **Brackets `[...]`**: elements become a `List`. If the last element is a
  spread (`...tail`), it becomes a `Cons` node instead.

### 2. Atoms

Pattern: no left/right child, closed form is a `CHead` with an atom token.

- `TAtom(Hole)` becomes `Hole(false)`
- `TAtom(Identifier(v))` becomes `Identifier(v)`
- `TAtom(StringLit(s))` becomes `StringLit(s)`

### 3. Keyword constructs (fun, let)

Pattern: closed form is a `CMatch` with `fun` or `let` as the head.

- **`fun(pat)=>`**: the interior items become the pattern, the right child
  becomes the body. Produces `Fun(pat, body)`.
- **`let(binding)in`**: the interior items become the binding, the right child
  becomes the body. Produces `Let(binding, body)`.

### 4. Infix operators

Pattern: closed form is a `CHead` with a named token (`:`, `->`, `=`, or any
other named token).

Specific tokens get specific constructors:
- `:` produces `Asc(left, right)`
- `->` produces `Arrow(left, right)`
- `=` produces `Eq(left, right)`

Any other named token with children falls through to `BinOp(op, left, right)`.
A named token with no children is treated as an `Identifier`.

### 5. Match chains

Pattern: closed form ends with `end`, and `isMatchChain` returns true.

The builder detects the `match...with...|...=>...end` nesting pattern by
recursively checking the `CMatch` tree. It then uses `collectMatchBranches` to
walk inward:

- The innermost `CMatch(CHead("match"), scrutItems, "with")` yields the
  scrutinee.
- Each `CMatch(CMatch(deeper, patItems, "=>"), bodyItems, "|" or "end")` layer
  yields one `(pattern, body)` branch.

The branches are collected in source order and produce `Match(scrutinee, branches)`.

### 6. If chains

Pattern: closed form ends with `end`, and `isIfChain` returns true.

The builder detects the `if...then...else...end` nesting pattern. It destructures
the four-deep `CMatch` nesting to extract the condition, then-branch, and
else-branch, producing `If(cond, thenBr, elseBr)`.

### 7. Block sequences

Pattern: closed form ends with `end` (and is neither a match nor an if chain).

The builder dispatches to `buildBlocks`, which recurses through nested `CMatch`
layers. Each layer corresponds to one block keyword (`postulate`, `meta`,
`construct`, `by`). The innermost block becomes the root, and outer blocks chain
via the `rest` parameter:

- `Postulate(body, rest)` -- the `rest` links to the next block
- `Meta(body, rest)`
- `Construct(name, decls, rest)` -- `name` is the schema identifier

## Bracket element collection

`collectBracketElements` walks the nested `CMatch` tree from inside out. Each
layer separated by a comma token (`,`, `,p`, `,l`) or a closing bracket token
(`)`, `]`) contributes one element group. The opening bracket token (`(` or `[`)
terminates the walk.

For example, `(a, b, c)` produces the nesting:
```
CMatch(CMatch(CMatch(CHead("("), [a], ",p"), [b], ",p"), [c], ")")
```

Walking inward collects `[c]`, then `[b]`, then `[a]`, yielding three element
groups in source order after reversal.

## Match chain detection

`isMatchChain` checks whether a `closedForm` represents a valid
`match...with...end` structure by recursively examining the token names:

- The outermost token must be `end`, `=>`, `|`, or `with`
- Recursing inward through `CMatch`, the innermost `CHead` must be `match`

This distinguishes match expressions from other `end`-terminated constructs
(blocks, if-chains) so `buildForm` can dispatch correctly.

## Key helpers

- **`combineTerms`**: given a list of terms, produces `Hole` (empty), the single
  term (singleton), or `Ap(first, rest)` (application).
- **`buildChild`**: builds a term from an optional right child plus unforms.
- **`buildLeftChild`**: builds a term from an optional left child plus unforms,
  wrapping in `Asc` if needed for type ascriptions.
- **`buildInfix`**: builds any infix operator by combining left child, right
  child, and localizing to the operator token's position.
- **`buildItems`**: extracts only the `Form` entries from a sharded list,
  ignoring `Unform` entries. Used for block contents where each declaration is a
  separate form.

## Tests

After implementing assignments 1-5, all 146 parse tests pass:
```bash
make test
```
