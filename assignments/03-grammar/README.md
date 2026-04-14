# Assignment 3: Grammar

## Overview

Define the Lytr language grammar. The grammar is pure data: a collection of
token definitions and match rules that the parser uses to lex, match brackets,
and structure the token stream into a parse tree.

`Grammar.re` (provided) defines the framework. Your job is to fill in
`LytrGrammar.re` with the specific tokens and rules for the Lytr language.

## File to implement

- **LytrGrammar.re** — the `grammar` binding

## How it works

A grammar consists of:

1. **Token definitions** — each token has a name, a kind (Keyword or Symbol),
   and left/right precedences
2. **Match rules** — which tokens pair up during the matching phase of parsing

### Token kinds

- `Keyword(s)` — alphabetic tokens like `postulate`, `match`, `let`
- `Symbol(s)` — punctuation tokens like `(`, `:`, `->`
- `AtomIdent` — virtual tokens created by morphing (never lexed directly)

### Precedence

Each token has a left and right precedence. During parsing, a token captures
children on each side based on precedence comparison with neighbors.

Three kinds of precedence, ordered `Interior < Precedence(n) < Uninterested`:

- **Interior** — greedily captures everything. Used for the "inside" edge of
  brackets. Example: `(` has rightPrec=Interior because it captures everything
  to its right until the matching `)`.
- **Precedence(n)** — a numeric level. Lower numbers bind more loosely.
  Example: `=` at 0.2/0.3 binds looser than `:` at 1.0/1.1.
- **Uninterested** — captures nothing. Used for atoms and the "outside" edge
  of brackets. Example: `)` has rightPrec=Uninterested because nothing to its
  right belongs inside the parens.

For infix operators: `left < right` means left-associative (e.g., `=` at
0.2/0.3), `left > right` means right-associative (e.g., `->` at 2.0/1.9).

### Match rules

The parser's matching phase pairs up tokens. Four rule types:

- **MatchPair(open, close)** — simple bracket matching.
  Example: `MatchPair("(", ")")` matches parens.

- **MatchPairMorph(open, token, morphTo)** — matches and replaces the right
  token with a new virtual token. Used for commas inside brackets:
  `MatchPairMorph("(", ",", ",p")` turns a `,` inside parens into `,p`,
  preventing `(a, b]` mismatches.

- **MatchBlockEnd(keyword, close)** — matches a block keyword with its closing
  token. Example: `MatchBlockEnd("postulate", "end")` pairs the block opener
  with `end`.

- **MatchBlockBlock(keyword1, keyword2)** — matches one block keyword with
  another. Example: `MatchBlockBlock("postulate", "meta")` allows
  `postulate...meta...end` chains.

## Grammar API

Use these functions from `Grammar.re`:

- `addToken(name, {kind, leftPrec, rightPrec}, g)` — add a raw token
- `addKeyword(name, ~leftPrec, ~rightPrec, g)` — add a keyword (shorthand)
- `addSymbol(name, ~symbol, ~leftPrec, ~rightPrec, g)` — add a symbol
- `addInfix(name, ~symbol, ~left, ~right, g)` — add an infix operator
- `addParens(open_, close, g)` — add matched brackets (adds tokens + MatchPair)
- `addBlock(keyword, ~close, g)` — add a block keyword (adds keyword token + MatchBlockEnd)
- `addMatch(rule, g)` — add a match rule

## What to define

### Block keywords
`postulate`, `meta`, `construct` — these open block sequences closed by `end`.

### Bracket pairs with comma morphing
`(...)` and `[...]` with commas that morph to context-specific variants
(`,p` inside parens, `,l` inside brackets) to prevent cross-bracket mismatches.

### Infix operators
`=`, `:`, `->`, `!=`, `==`, `&&`, `||` — with appropriate precedences.

### Matched keyword constructs
- `match...with...|...=>...end` — pattern matching
- `fun...=>f` — lambda (=> morphs to =>f so it doesn't match `end`)
- `if...then...else...end` — conditionals
- `let...in` — local bindings

### Atom keywords
- `schema` — definition marker inside meta blocks
- `_` and `...` — wildcard and spread symbols

### Block keyword chaining
- Each block keyword matches `end` (via `addBlock`)
- Each block keyword matches every other block keyword (via MatchBlockBlock)
- `construct...by` is a matched pair; `by` inherits block-end/block-block matching

## Tests

After implementing assignments 1-5, all 146 parse tests pass:
```bash
make test
```

The grammar itself doesn't have isolated tests — it's exercised by the parser.
