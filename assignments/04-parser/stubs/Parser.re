open Utils;
open Grammar;

/* ---------- Types shared across both phases ---------- */

type unform =
  | USecondary(ranged(secondaryToken))
  | UShard(ranged(primaryToken));

type sharded('t) =
  | Unform(unform)
  | Form('t);

/* ====================================================
   PHASE 1: MATCHING
   Establishes bracket/delimiter matching relationships.
   Precedence is not considered yet.
   ==================================================== */

type partialForm =
  | Head(ranged(primaryToken))
  | PMatch(partialForm, list(sharded(partialForm)), ranged(primaryToken));

let faceOf =
  fun
  | Head(token) | PMatch(_, _, token) => token;

let asPrimary = (t: ranged(token)): ranged(primaryToken) =>
  mapRanged(
    fun
    | Primary(p) => p
    | Secondary(_) => failwith("asPrimary called on secondary token"),
    t,
  );

let asSecondary = (t: ranged(token)): ranged(secondaryToken) =>
  mapRanged(
    fun
    | Secondary(s) => s
    | Primary(_) => failwith("asSecondary called on primary token"),
    t,
  );

/* Disassemble a partialForm back into a flat list of shards.
   Head(token) => [Unform(UShard(token))]
   PMatch(form, items, token) => shatter(form) @ items @ [Unform(UShard(token))] */
let rec shatter =
  fun
  | Head(_token) => failwith("TODO: shatter Head")
  | PMatch(_form, _items, _token) => failwith("TODO: shatter PMatch");

/* Finalize a partial form: if its face is a valid end token, keep it as
   [Form(f)]; otherwise shatter it back into shards. */
let finalize = (_g, _f: partialForm): list(sharded(partialForm)) =>
  failwith("TODO: finalize");

/* Apply finalize to every Form in a list; Unform items pass through. */
let flattenStack = (_g) =>
  fun
  | _ => failwith("TODO: flattenStack");

/* Search the (reversed) stack for a form whose face matches token t.
   Accumulate skipped items. On match, reconstruct the stack with a
   PMatch. Returns None if no match found.

   Use matchToken(g, faceOf(form).value, t.value) to check for matches.
   matchToken returns Match, MatchMorph(morphed), or NoMatch.

   On Match: Some(List.rev(rest) @ [Form(PMatch(form, flattenStack(g, skipped), t))])
   On MatchMorph(morphed): same, but replace t's value with morphed. */
let rec findMatch =
        (
          _g: grammar,
          _stack: list(sharded(partialForm)),
          _t: ranged(primaryToken),
          _skipped: list(sharded(partialForm)),
        )
        : option(list(sharded(partialForm))) =>
  failwith("TODO: findMatch");

/* Process one token:
   - Secondary tokens: append as Unform(USecondary(...))
   - Primary tokens: try findMatch on the reversed stack.
     If found, use the result.
     If not found: if isValidStart, push Form(Head(...));
     otherwise push Unform(UShard(...)). */
let matchPush = (_g, _stack, _t: ranged(token)) =>
  failwith("TODO: matchPush");

/* Run matchPush over all tokens, bookended with BOF and EOF.
   BOF/EOF match each other, so the result should be a single
   PMatch(Head(BOF), items, EOF). Extract and return the items. */
let matchParse = (_g, _ts: list(ranged(token))): list(sharded(partialForm)) =>
  failwith("TODO: matchParse");

/* ====================================================
   PHASE 2: OPERATORIZE
   Uses operator precedence to assign left/right children
   to matched forms. Shift-reduce-roll algorithm.
   ==================================================== */

type closedForm =
  | CHead(ranged(primaryToken))
  | CMatch(closedForm, list(sharded(openForm)), ranged(primaryToken))
and openForm = {
  left: option(openForm),
  leftUf: list(unform),
  closed: closedForm,
  rightUf: list(unform),
  right: option(openForm),
};

type halfOpenForm = {
  hLeft: option(openForm),
  hLeftUf: list(unform),
  hClosed: closedForm,
  hRightUf: list(unform),
};

let rec headOf =
  fun
  | CHead(token) => token
  | CMatch(form, _, _) => headOf(form);

let faceOfClosed =
  fun
  | CHead(token) | CMatch(_, _, token) => token;

type comparison =
  | Shift
  | Reduce
  | Roll;

let mkOpen = (~left=None, ~leftUf=[], ~rightUf=[], ~right=None, closed) =>
  {left, leftUf, closed, rightUf, right};

let mkHalf = (~left=None, ~leftUf=[], ~rightUf=[], closed) =>
  {hLeft: left, hLeftUf: leftUf, hClosed: closed, hRightUf: rightUf};

let closeHalf = (~right=None, ~rightUf=?, h: halfOpenForm) =>
  mkOpen(
    ~left=h.hLeft,
    ~leftUf=h.hLeftUf,
    ~rightUf=
      switch (rightUf) {
      | Some(uf) => uf
      | None => h.hRightUf
      },
    ~right,
    h.hClosed,
  );

/* --- Stack state for the operatorize phase --- */

type opState = {
  completed: list(sharded(openForm)),
  halfOpen: list(halfOpenForm),
};

let unsnoc = lst => {
  let rev = List.rev(lst);
  (List.rev(List.tl(rev)), List.hd(rev));
};

/* Compare precedences of two tokens.
   Compare rightPrec(g, t1) vs leftPrec(g, t2):
   - Both Precedence: lower number = looser. r < l => Shift, r > l => Reduce, equal => error
   - Uninterested vs Precedence: Uninterested yields (right=Uninterested => Reduce, left=Uninterested => Shift)
   - Both Uninterested => Roll
   - Interior should never appear here */
let compare = (_g, _t1: primaryToken, _t2: primaryToken): comparison =>
  failwith("TODO: compare");

/* Does this token want a left operand?
   True if leftPrec(g, t) is Precedence(_). */
let wantsLeftChild = (_g, _t) =>
  failwith("TODO: wantsLeftChild");

/* Finalize the half-open stack by closing each half-open form.
   Walk from most-recent to least-recent:
   - If acc is Some(a), attach it as the right child of the current half-open form
   - If acc is None, close with no right child and move trailing unforms to completed
   Base case: empty stack -> return completed (with acc appended if Some) */
let rec roll =
        (_completed: list(sharded(openForm)), _halfOpen: list(halfOpenForm), _acc: option(openForm))
        : list(sharded(openForm)) =>
  failwith("TODO: roll");

/* Convenience: call roll with the state's fields. */
let rollState = (_s: opState, _acc) =>
  failwith("TODO: rollState");

/* The core Pratt parser logic. Push a closed form into the operator state.
   Compare against the top of the half-open stack:
   - Empty stack, no acc: start a new half-open form
   - Empty stack, has acc + form wants left child: make acc the left child
   - Shift: new form binds tighter, push new half-open
   - Reduce: stack top binds tighter, close it (attach acc as right), recurse
   - Roll: finalize everything, start fresh with just the new form */
let rec pushForm =
        (_g, _os: opState, _acc: option(openForm), _seAcc: list(unform), _f: closedForm)
        : opState =>
  failwith("TODO: pushForm");

/* Handle a sharded item in the operatorize phase.
   - USecondary: attach to rightmost half-open form's trailing unforms,
     or append to completed if stack is empty
   - UShard: roll everything and append the shard to completed
   - Form: delegate to pushForm */
let pushSharded = (_g, _os: opState, _f: sharded(closedForm)): opState =>
  failwith("TODO: pushSharded");

/* Convert a partialForm to a closedForm, recursively operatorizing interior items. */
let rec closePartial = (_g) =>
  fun
  | Head(_token) => failwith("TODO: closePartial Head")
  | PMatch(_form, _items, _token) => failwith("TODO: closePartial PMatch")
/* Map closePartial over a sharded item. Unforms pass through. */
and closeShardedPartial = (_g) =>
  fun
  | Unform(_u) => failwith("TODO: closeShardedPartial Unform")
  | Form(_form) => failwith("TODO: closeShardedPartial Form")
/* Main operator precedence pass.
   Fold over input: convert each item via closeShardedPartial,
   push via pushSharded. After all items, roll the final state. */
and operatorize = (_g, _fs: list(sharded(partialForm))): list(sharded(openForm)) =>
  failwith("TODO: operatorize");

/* Full pipeline: matchParse then operatorize. */
let parse = (_g, _tokens: list(ranged(token))): list(sharded(openForm)) =>
  failwith("TODO: parse");
