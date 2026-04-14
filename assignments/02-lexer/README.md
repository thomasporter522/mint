# Assignment 2: Lexer

## Overview

Implement the tokenizer that converts source text into a token stream.
The lexer is grammar-aware: it uses the grammar's keyword and symbol maps
to recognize tokens.

## File to implement

- **Lexer.re** — the `lex` function

## How it works

The lexer processes characters left to right, emitting tokens:

1. **Whitespace** — spaces, tabs, newlines → `Secondary(Whitespace(s))`
2. **Line comments** — `--` to end of line → `Secondary(Whitespace(s))`
3. **String literals** — `"..."` → `Primary(TAtom(StringLit(content)))`
4. **Identifiers/keywords** — letter followed by alphanum/underscore/hyphen.
   Look up in the grammar's `keywordMap`: if found → `Primary(TNamed(name))`,
   otherwise → `Primary(TAtom(Identifier(word)))`
5. **Holes** — bare `?` → `Primary(TAtom(Hole))`.
   `?` followed by a letter → `Primary(TAtom(Identifier("?" ++ name)))`
6. **Symbols** — try to match against grammar's `symbolMap`, greedy (longest first).
   Matched → `Primary(TNamed(name))`. Unmatched → `Secondary(Unlexed(c))`

Each token is wrapped in `{value, start, end_}` with character offsets.
Return the list in order (the implementation accumulates in reverse, so
reverse at the end).

## Character classification

- `isWhitespace`: space, tab, newline, carriage return
- `isDigit`: '0'-'9'
- `isLetter`: 'a'-'z', 'A'-'Z'
- `isAlphanum`: letter, digit, underscore, or hyphen

## Tests

After assignment 5, parse tests will exercise the lexer indirectly.
