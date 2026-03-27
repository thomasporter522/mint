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

let rec shatter =
  fun
  | Head(token) => [Unform(UShard(token))]
  | PMatch(form, items, token) =>
    shatter(form) @ items @ [Unform(UShard(token))];

let finalize = (f: partialForm): list(sharded(partialForm)) =>
  isValidEnd(faceOf(f)) ? [Form(f)] : shatter(f);

let flattenStack =
  List.concat_map(
    fun
    | Unform(_) as u => [u]
    | Form(f) => finalize(f),
  );

let rec findMatch =
        (
          stack: list(sharded(partialForm)),
          t: ranged(primaryToken),
          skipped: list(sharded(partialForm)),
        )
        : option(list(sharded(partialForm))) =>
  switch (stack) {
  | [] => None
  | [Unform(_) as u, ...rest] => findMatch(rest, t, [u, ...skipped])
  | [Form(form), ...rest] =>
    switch (matchToken(faceOf(form).value, t.value)) {
    | NoMatch => findMatch(rest, t, [Form(form), ...skipped])
    | MatchMorph(morphed) =>
      let t' = {value: morphed, start: t.start, end_: t.end_};
      Some(List.rev(rest) @ [Form(PMatch(form, flattenStack(skipped), t'))])
    | Match =>
      Some(List.rev(rest) @ [Form(PMatch(form, flattenStack(skipped), t))])
    }
  };

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

let matchPush = (stack, t: ranged(token)) =>
  switch (t.value) {
  | Secondary(_) => stack @ [Unform(USecondary(asSecondary(t)))]
  | Primary(pt) =>
    switch (findMatch(List.rev(stack), asPrimary(t), [])) {
    | Some(result) => result
    | None =>
      let item =
        isValidStart(pt) ? Form(Head(asPrimary(t))) : Unform(UShard(asPrimary(t)));
      stack @ [item];
    }
  };

let matchParse = (ts: list(ranged(token))): list(sharded(partialForm)) => {
  let bof = {value: Primary(BOF), start: (-1), end_: (-1)};
  let eof = {value: Primary(EOF), start: (-1), end_: (-1)};
  let result = List.fold_left(matchPush, [], [bof, ...ts] @ [eof]);

  switch (result) {
  | [Form(PMatch(Head({value: BOF, _}), items, {value: EOF, _}))] => items
  | _ => failwith("Parser invariant violated: expected BOF...EOF wrapper")
  };
};

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

let compare = (t1: primaryToken, t2: primaryToken): comparison =>
  switch (rightPrec(t1), leftPrec(t2)) {
  | (Precedence(r), Precedence(l)) when r < l => Shift
  | (Precedence(r), Precedence(l)) when r > l => Reduce
  | (Precedence(_), Precedence(_))  => failwith("Precedence collision")
  | (Uninterested,  Precedence(_))  => Reduce
  | (Precedence(_), Uninterested)   => Shift
  | (Uninterested,  Uninterested)   => Roll
  | _ => failwith("Precondition violated: Interior precedence in compare")
  };

let wantsLeftChild = t =>
  switch (leftPrec(t)) {
  | Precedence(_) => true
  | _ => false
  };

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

/* Snoc-list helper: split off last element */
let unsnoc = lst => {
  let rev = List.rev(lst);
  (List.rev(List.tl(rev)), List.hd(rev));
};

/* Roll up the half-open stack, folding rightward into a single open form. */
let rec roll =
        (completed: list(sharded(openForm)), halfOpen: list(halfOpenForm), acc: option(openForm))
        : list(sharded(openForm)) =>
  switch (halfOpen, acc) {
  | ([], None) => completed
  | ([], Some(a)) => completed @ [Form(a)]
  | ([h, ...rest], None) =>
    let trailing = List.map(u => Unform(u), h.hRightUf);
    roll(completed, rest, Some(closeHalf(~rightUf=[], h))) @ trailing;
  | ([h, ...rest], Some(a)) =>
    roll(completed, rest, Some(closeHalf(~right=Some(a), h)))
  };

let rollState = (s: opState, acc) =>
  roll(s.completed, List.rev(s.halfOpen), acc);

let rec pushForm =
        (os: opState, acc: option(openForm), seAcc: list(unform), f: closedForm)
        : opState =>
  switch (os.halfOpen) {
  | [] =>
    switch (acc) {
    | None =>
      {completed: os.completed, halfOpen: [mkHalf(f)]}
    | Some(_) when wantsLeftChild(headOf(f).value) =>
      {completed: os.completed, halfOpen: [mkHalf(~left=acc, ~leftUf=seAcc, f)]}
    | _ =>
      failwith("pushForm: unexpected accumulator without left-child demand")
    }

  | _ =>
    let (rest, face) = unsnoc(os.halfOpen);
    switch (compare(faceOfClosed(face.hClosed).value, headOf(f).value)) {
    | Shift =>
      let newHalf = mkHalf(~left=acc, ~leftUf=seAcc, f);
      {completed: os.completed, halfOpen: os.halfOpen @ [newHalf]};

    | Reduce =>
      let (accPrime, seAccPrime) =
        switch (acc) {
        | None => (Some(closeHalf(~rightUf=[], face)), face.hRightUf @ seAcc)
        | Some(a) => (Some(closeHalf(~right=Some(a), face)), seAcc)
        };
      pushForm({completed: os.completed, halfOpen: rest}, accPrime, seAccPrime, f);

    | Roll =>
      let trailing = List.map(u => Unform(u), seAcc);
      let completed = rollState(os, acc) @ trailing;
      {completed, halfOpen: [mkHalf(f)]};
    };
  };

let pushSharded = (os: opState, f: sharded(closedForm)): opState =>
  switch (f) {
  | Unform(USecondary(_) as u) =>
    switch (os.halfOpen) {
    | [] =>
      {completed: os.completed @ [Unform(u)], halfOpen: []}
    | _ =>
      let (rest, last) = unsnoc(os.halfOpen);
      let last = {...last, hRightUf: last.hRightUf @ [u]};
      {completed: os.completed, halfOpen: rest @ [last]};
    }
  | Unform(UShard(_) as u) =>
    {completed: rollState(os, None) @ [Unform(u)], halfOpen: []}
  | Form(form) =>
    pushForm(os, None, [], form)
  };

let rec closePartial =
  fun
  | Head(token) => CHead(token)
  | PMatch(form, items, token) =>
    CMatch(closePartial(form), operatorize(items), token)
and closeShardedPartial =
  fun
  | Unform(u) => Unform(u)
  | Form(form) => Form(closePartial(form))
and operatorize = (fs: list(sharded(partialForm))): list(sharded(openForm)) => {
  let state = List.fold_left(
    (s, f) => pushSharded(s, closeShardedPartial(f)),
    {completed: [], halfOpen: []},
    fs,
  );
  rollState(state, None);
};

let parse = (tokens: list(ranged(token))): list(sharded(openForm)) =>
  operatorize(matchParse(tokens));
