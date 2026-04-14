# Assignment 4: Parser

## Overview

Implement a two-phase parser that transforms a flat token stream into a
structured tree with matched brackets and operator precedence. The parser
is generic: it takes a grammar as a parameter and works with any grammar
definition.

This is the hardest assignment. The bracket matching phase is
straightforward, but the operator precedence phase uses a variant of Pratt
parsing with a shift-reduce-roll algorithm that requires careful reasoning
about precedence comparisons and stack manipulation.

Read `Grammar.re` first to understand the token types (`primaryToken`,
`secondaryToken`, `token`, `precedence`) and the grammar query functions
(`leftPrec`, `rightPrec`, `matchToken`, `isValidStart`, `isValidEnd`).

## File to implement

- **Parser.re** — bracket matching, operator precedence, and the full parse pipeline

## Data types

The parser uses two layers of types, one per phase:

**Shared types:**
- `unform` — a token that has no structure: either a `USecondary` (whitespace/unlexed) or a `UShard` (a primary token that didn't match anything)
- `sharded('t)` — either an `Unform(unform)` or a `Form('t)` — a structured item interleaved with unstructured debris

**Phase 1 (matching) types:**
- `partialForm` — a matched bracket structure. `Head(token)` is a single open bracket; `PMatch(form, items, token)` is a matched pair wrapping its head form, interior items, and closing token

**Phase 2 (operatorize) types:**
- `closedForm` — like `partialForm` but recursively operatorized inside. `CHead(token)` or `CMatch(closedForm, items, token)`
- `openForm` — a closed form with optional left and right children (set by operator precedence) and unform debris on each side
- `halfOpenForm` — an open form under construction: has a left child but no right child yet (waiting for the next token to decide)
- `opState` — the shift-reduce state: a list of completed sharded open forms, plus a stack of half-open forms being built
- `comparison` — the result of comparing two tokens' precedences: `Shift`, `Reduce`, or `Roll`

## Phase 1: Bracket matching

The matching phase processes tokens left to right, maintaining a stack
of partially-matched forms. When a closing token arrives, it searches the
stack for a matching opener (using the grammar's `matchToken` function).

Data flows: `list(ranged(token))` -> `list(sharded(partialForm))`

### Functions

**`shatter(partialForm) -> list(sharded(partialForm))`**
Disassemble a partial form back into a flat list of shards. A `Head(token)` becomes `[Unform(UShard(token))]`. A `PMatch(form, items, token)` recursively shatters the head form, appends the interior items, and appends the closing token as a shard.

**`finalize(grammar, partialForm) -> list(sharded(partialForm))`**
Decide whether a partial form is valid. If its face token is a valid end token (according to the grammar), keep it as `[Form(f)]`. Otherwise, shatter it — it was a false start.

**`flattenStack(grammar, list(sharded(partialForm))) -> list(sharded(partialForm))`**
Apply `finalize` to every `Form` in a list. `Unform` items pass through unchanged.

**`findMatch(grammar, stack, token, skipped) -> option(list(sharded(partialForm)))`**
Search the reversed stack for a form whose face matches the incoming token. Walk backwards through the stack, accumulating skipped items. When a match is found, reconstruct the stack with a new `PMatch` form containing the matched opener, the flattened skipped items as interior, and the closing token. Returns `None` if no match is found.

The grammar's `matchToken` may return `Match` (use the token as-is), `MatchMorph(morphed)` (replace the token with a morphed version — used for comma disambiguation), or `NoMatch`.

**`matchPush(grammar, stack, token) -> stack`**
Process one token. If it's secondary, append as `Unform`. If primary, try `findMatch` on the reversed stack. If a match is found, use the result. Otherwise, if the token is a valid start (according to the grammar), push as `Form(Head(...))`. Otherwise push as `Unform(UShard(...))`.

**`matchParse(grammar, tokens) -> list(sharded(partialForm))`**
Run `matchPush` over all tokens, bookended by synthetic BOF and EOF tokens. BOF and EOF match each other via the grammar, so the result should be a single `PMatch(Head(BOF), items, EOF)`. Extract and return the interior items.

## Phase 2: Operator precedence (operatorize)

The operatorize phase assigns left and right children to matched forms
based on operator precedence. It uses a shift-reduce-roll algorithm.

Data flows: `list(sharded(partialForm))` -> `list(sharded(openForm))`

The key insight: each token has a left precedence (how strongly it binds
to the left) and a right precedence (how strongly it binds to the right).
When two adjacent tokens compete for an operand between them, the one with
the stronger precedence wins.

### Precedence comparison

**`compare(grammar, token1, token2) -> comparison`**
Compare the right precedence of token1 against the left precedence of token2:
- Both are `Precedence(float)`: lower number = looser binding. If `right < left`, the new token binds tighter -> `Shift`. If `right > left`, the existing token binds tighter -> `Reduce`. Equal precedences are an error (collision).
- `Uninterested` vs `Precedence(_)`: the uninterested side yields. Right=Uninterested -> `Reduce`; Left=Uninterested -> `Shift`.
- Both `Uninterested` -> `Roll` (neither wants the operand; they are independent items at the same level).
- `Interior` should never appear in `compare` — it means the token is a bracket delimiter, which was already handled in phase 1.

**`wantsLeftChild(grammar, token) -> bool`**
Returns true if the token's left precedence is a `Precedence(_)` value. Atoms and openers have `Uninterested` left precedence and don't want a left child.

### Stack operations

The operator phase maintains an `opState`: a list of fully `completed` items and a stack of `halfOpen` forms (forms that have been seen but might still acquire a right child).

**`roll(completed, halfOpen, acc) -> list(sharded(openForm))`**
Finalize the half-open stack by closing each half-open form. Walk the stack from most-recent to least-recent. If there's an accumulator (a right child from a previous step), attach it. Otherwise, close the half-open form with no right child and move any trailing unforms to the completed list.

**`rollState(opState, acc) -> list(sharded(openForm))`**
Convenience: call `roll` with the state's completed and reversed half-open stack.

**`pushForm(grammar, opState, acc, seAcc, closedForm) -> opState`**
The core of the Pratt parser. Push a new closed form into the operator state. Compare it against the top of the half-open stack:
- **Empty stack, no accumulator**: start a new half-open form.
- **Empty stack, has accumulator**: if the new form wants a left child, make it the left child. Otherwise error.
- **Shift**: the new form binds tighter than the stack top. Push a new half-open form onto the stack.
- **Reduce**: the stack top binds tighter. Close the stack top (attaching the accumulator as its right child, or trailing the unforms if no accumulator), then recurse with the closed form as the new accumulator.
- **Roll**: neither token wants the operand. Finalize the entire stack, start fresh with just the new form.

**`pushSharded(grammar, opState, sharded(closedForm)) -> opState`**
Handle a sharded item:
- `USecondary`: if there's a half-open stack, attach to the rightmost half-open form's trailing unforms. Otherwise append to completed.
- `UShard`: roll the entire state and append the shard to completed.
- `Form`: delegate to `pushForm`.

### Conversion and main loop

**`closePartial(grammar, partialForm) -> closedForm`**
Convert a partial form (from phase 1) into a closed form (for phase 2). Recursively operatorize the interior items.

**`closeShardedPartial(grammar, sharded(partialForm)) -> sharded(closedForm)`**
Map `closePartial` over a sharded item. Unforms pass through.

**`operatorize(grammar, list(sharded(partialForm))) -> list(sharded(openForm))`**
The main operator precedence pass. Fold over the input: convert each item to a closed form via `closeShardedPartial`, then push it via `pushSharded`. After processing all items, roll the final state.

## Phase 3: Integration

**`parse(grammar, list(ranged(token))) -> list(sharded(openForm))`**
The full pipeline: run `matchParse` to establish bracket structure, then `operatorize` to assign operator children.

## Example

Given input `f x + g y`:
1. Lexer produces: `[f, " ", x, " ", +, " ", g, " ", y]`
2. Match phase (with BOF/EOF): since `+` is an infix operator (not a bracket), nothing matches. Result: `[Form(Head(f)), Unform(WS), Form(Head(x)), Unform(WS), Form(Head(+)), ...]`
   - Actually, atoms (`f`, `x`, `g`, `y`) are not valid starts in the grammar (their left prec is `Uninterested`, and `isValidStart` checks left prec != Interior, so atoms ARE valid starts). They become `Form(Head(...))`.
3. Operatorize: `+` has left and right precedence. It shifts past `f` and `x` (which have `Uninterested` right prec -> `Roll`), then `f` and `x` roll together (function application). Similarly for `g` and `y`. Then `+` reduces, getting the `f x` application as its left child and `g y` as its right.

## Hints

- The matching phase processes the stack in reverse (most recent first) when searching for matches, but stores it in forward order.
- `flattenStack` is important: when items are skipped during matching, they need to be finalized. A partially-matched form that turns out to be invalid gets shattered back into shards.
- In the operatorize phase, the `seAcc` parameter in `pushForm` accumulates secondary (whitespace) unforms that haven't been assigned to a form yet. When reducing, these get threaded through correctly.
- `Roll` is the "these are siblings, not parent-child" case. It happens between atoms at the same level (like function arguments) and between keyword atoms.

## Tests

After implementing, you can test end-to-end with assignment 5 (Builder) or
by checking intermediate representations manually:
```bash
make reason
make test
```
