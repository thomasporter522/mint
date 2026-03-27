open Utils;
open Grammar;

type unform =
  | USecondary(ranged(secondaryToken))
  | UShard(ranged(primaryToken));

type sharded('t) =
  | Unform(unform)
  | Form('t);

type partialForm =
  | Head(ranged(primaryToken))
  | PMatch(partialForm, list(sharded(partialForm)), ranged(primaryToken));

let faceOfPartialForm = (pf: partialForm): ranged(primaryToken) =>
  switch (pf) {
  | Head(token) => token
  | PMatch(_, _, token) => token
  };

/* MATCHING PHASE */

let rec shatterPartialForm =
        (pf: partialForm): list(sharded(partialForm)) =>
  switch (pf) {
  | Head(token) => [Unform(UShard(token))]
  | PMatch(form, items, token) =>
    shatterPartialForm(form) @ items @ [Unform(UShard(token))]
  };

let flattenPartialForm =
    (f: partialForm): list(sharded(partialForm)) =>
  if (isValidEnd(faceOfPartialForm(f))) {
    [Form(f)];
  } else {
    shatterPartialForm(f);
  };

let flatten =
    (spfs: list(sharded(partialForm))): list(sharded(partialForm)) =>
  List.concat_map(
    spf =>
      switch (spf) {
      | Unform(_) => [spf]
      | Form(f) => flattenPartialForm(f)
      },
    spfs,
  );

type matchStackResult =
  | MSNoMatch
  | MSMatch(list(sharded(partialForm)));

let rec matchStack =
        (
          s: list(sharded(partialForm)),
          t: ranged(primaryToken),
          sSkipped: list(sharded(partialForm)),
        )
        : matchStackResult =>
  switch (s) {
  | [] => MSNoMatch
  | [last, ...rest] =>
    switch (last) {
    | Unform(_) => matchStack(rest, t, [last, ...sSkipped])
    | Form(form) =>
      let matchResult =
        matchToken(faceOfPartialForm(form).value, t.value);
      switch (matchResult) {
      | NoMatch => matchStack(rest, t, [last, ...sSkipped])
      | MatchMorph(morphed) =>
        let newForm =
          PMatch(
            form,
            flatten(sSkipped),
            {value: morphed, start: t.start, end_: t.end_},
          );
        MSMatch(List.rev(rest) @ [Form(newForm)]);
      | Match =>
        let newForm = PMatch(form, flatten(sSkipped), t);
        MSMatch(List.rev(rest) @ [Form(newForm)]);
      };
    }
  };

/* Process from right: reverse list, process, reverse back */
let matchStackRightToLeft =
    (
      s: list(sharded(partialForm)),
      t: ranged(primaryToken),
    )
    : matchStackResult => {
  let reversed = List.rev(s);
  switch (matchStack(reversed, t, [])) {
  | MSNoMatch => MSNoMatch
  | MSMatch(result) => MSMatch(result)
  };
};

let getPrimaryToken = (t: ranged(token)): ranged(primaryToken) =>
  mapRanged(
    tok =>
      switch (tok) {
      | Primary(p) => p
      | Secondary(_) => BOF /* should never happen */
      },
    t,
  );

let getSecondaryToken = (t: ranged(token)): ranged(secondaryToken) =>
  mapRanged(
    tok =>
      switch (tok) {
      | Primary(_) => Whitespace("") /* should never happen */
      | Secondary(s) => s
      },
    t,
  );

let matchPush =
    (s: list(sharded(partialForm)), t: ranged(token))
    : list(sharded(partialForm)) =>
  switch (t.value) {
  | Secondary(_) => s @ [Unform(USecondary(getSecondaryToken(t)))]
  | Primary(primaryTok) =>
    let pt = getPrimaryToken(t);
    switch (matchStackRightToLeft(s, pt)) {
    | MSMatch(result) => result
    | MSNoMatch =>
      if (isValidStart(primaryTok)) {
        s @ [Form(Head(pt))];
      } else {
        s @ [Unform(UShard(pt))];
      }
    };
  };

let matchPushes =
    (s: list(sharded(partialForm)), ts: list(ranged(token)))
    : list(sharded(partialForm)) =>
  List.fold_left(matchPush, s, ts);

let matchParse =
    (ts: list(ranged(token))): list(sharded(partialForm)) => {
  let tokens = [
    {value: Primary(BOF), start: (-1), end_: (-1)},
    ...ts,
  ] @ [{value: Primary(EOF), start: (-1), end_: (-1)}];
  let result = matchPushes([], tokens);
  switch (result) {
  | [Form(PMatch(Head({value: BOF, _}), items, {value: EOF, _}))] => items
  | _ =>
    failwith(
      "Impossible matching - parser failed to create expected BOF...EOF structure",
    )
  };
};

/* OPERATORIZE PHASE */

type unforms = list(unform);

type closedForm =
  | CHead(ranged(primaryToken))
  | CMatch(closedForm, list(sharded(openForm)), ranged(primaryToken))
and openForm = {
  left: option(openForm),
  leftUnforms: unforms,
  closedForm,
  rightUnforms: unforms,
  right: option(openForm),
};

type halfOpenForm = {
  hoLeft: option(openForm),
  hoLeftUnforms: unforms,
  hoClosedForm: closedForm,
  hoRightUnforms: unforms,
};

let rec headOf = (cf: closedForm): ranged(primaryToken) =>
  switch (cf) {
  | CHead(token) => token
  | CMatch(form, _, _) => headOf(form)
  };

let faceOfForm = (cf: closedForm): ranged(primaryToken) =>
  switch (cf) {
  | CHead(token) => token
  | CMatch(_, _, token) => token
  };

let faceOfHalfOpenForm = (hof: halfOpenForm): ranged(primaryToken) =>
  faceOfForm(hof.hoClosedForm);

type compareTokensResult =
  | Shift
  | Reduce
  | Roll;

let compareTokens =
    (t1: primaryToken, t2: primaryToken): compareTokensResult => {
  let (_, rightPrec1) = getPrecedence(t1);
  let (leftPrec2, _) = getPrecedence(t2);
  switch (rightPrec1, leftPrec2) {
  | (Precedence(r), Precedence(l)) when r < l => Shift
  | (Precedence(r), Precedence(l)) when r > l => Reduce
  | (Precedence(_), Precedence(_)) =>
    failwith("Precedence collision")
  | (Uninterested, Precedence(_)) => Reduce
  | (Precedence(_), Uninterested) => Shift
  | (Uninterested, Uninterested) => Roll
  | _ => failwith("Precondition violated: Interior precedence found")
  };
};

let wantsLeftChild = (t: primaryToken): bool => {
  let (leftPrec, _) = getPrecedence(t);
  switch (leftPrec) {
  | Precedence(_) => true
  | _ => false
  };
};

type opState = {
  completed: list(sharded(openForm)),
  halfOpen: list(halfOpenForm),
};

let rec opStateRoll =
        (s: opState, acc: option(openForm)): list(sharded(openForm)) =>
  switch (s.halfOpen, acc) {
  | ([], None) => s.completed
  | ([], Some(a)) => s.completed @ [Form(a)]
  | ([lastHalf, ...restHalfs], None) =>
    let se2Prime =
      List.map(f => Unform(f), lastHalf.hoRightUnforms);
    let accPrime = {
      left: lastHalf.hoLeft,
      leftUnforms: lastHalf.hoLeftUnforms,
      closedForm: lastHalf.hoClosedForm,
      rightUnforms: [],
      right: None,
    };
    opStateRoll({completed: s.completed, halfOpen: restHalfs}, Some(accPrime))
    @ se2Prime;
  | ([lastHalf, ...restHalfs], Some(a)) =>
    let newAcc = {
      left: lastHalf.hoLeft,
      leftUnforms: lastHalf.hoLeftUnforms,
      closedForm: lastHalf.hoClosedForm,
      rightUnforms: lastHalf.hoRightUnforms,
      right: Some(a),
    };
    opStateRoll(
      {completed: s.completed, halfOpen: restHalfs},
      Some(newAcc),
    );
  }
/* Process halfOpen from right: list is stored in reverse order (rightmost last) */
and opStateRollFromRight =
  (s: opState, acc: option(openForm)): list(sharded(openForm)) => {
  let revState = {...s, halfOpen: List.rev(s.halfOpen)};
  opStateRoll(revState, acc);
};

let rec opPushForm =
        (
          os: opState,
          acc: option(openForm),
          seAcc: unforms,
          f: closedForm,
        )
        : opState =>
  switch (os.halfOpen) {
  | [] =>
    switch (acc) {
    | None => {
        completed: os.completed,
        halfOpen: [
          {
            hoLeft: None,
            hoLeftUnforms: [],
            hoClosedForm: f,
            hoRightUnforms: [],
          },
        ],
      }
    | Some(_) when wantsLeftChild(headOf(f).value) => {
        completed: os.completed,
        halfOpen: [
          {
            hoLeft: acc,
            hoLeftUnforms: seAcc,
            hoClosedForm: f,
            hoRightUnforms: [],
          },
        ],
      }
    | _ => failwith("I'm curious whether this is possible")
    }
  | _ =>
    /* Get last element (rightmost) */
    let revHalfs = List.rev(os.halfOpen);
    let face = List.hd(revHalfs);
    let restHalfs = List.rev(List.tl(revHalfs));
    let comparison =
      compareTokens(
        faceOfHalfOpenForm(face).value,
        headOf(f).value,
      );
    switch (comparison) {
    | Shift => {
        completed: os.completed,
        halfOpen:
          os.halfOpen
          @ [
            {
              hoLeft: acc,
              hoLeftUnforms: seAcc,
              hoClosedForm: f,
              hoRightUnforms: [],
            },
          ],
      }
    | Reduce =>
      switch (acc) {
      | None =>
        let accPrime = {
          left: face.hoLeft,
          leftUnforms: face.hoLeftUnforms,
          closedForm: face.hoClosedForm,
          rightUnforms: [],
          right: None,
        };
        opPushForm(
          {completed: os.completed, halfOpen: restHalfs},
          Some(accPrime),
          face.hoRightUnforms @ seAcc,
          f,
        );
      | Some(a) =>
        let accPrime = {
          left: face.hoLeft,
          leftUnforms: face.hoLeftUnforms,
          closedForm: face.hoClosedForm,
          rightUnforms: face.hoRightUnforms,
          right: Some(a),
        };
        opPushForm(
          {completed: os.completed, halfOpen: restHalfs},
          Some(accPrime),
          seAcc,
          f,
        );
      }
    | Roll =>
      let seAccPrime = List.map(f => Unform(f), seAcc);
      let completedPrime =
        opStateRollFromRight(os, acc) @ seAccPrime;
      {
        completed: completedPrime,
        halfOpen: [
          {
            hoLeft: None,
            hoLeftUnforms: [],
            hoClosedForm: f,
            hoRightUnforms: [],
          },
        ],
      };
    };
  };

/* ShardsObstructive mode (the active mode in the TS code) */
let opPush = (os: opState, f: sharded(closedForm)): opState =>
  switch (f) {
  | Unform(unform) =>
    switch (unform) {
    | USecondary(_) =>
      switch (os.halfOpen) {
      | [] => {
          completed: os.completed @ [Unform(unform)],
          halfOpen: [],
        }
      | _ =>
        let revHalfs = List.rev(os.halfOpen);
        let lastHalf = List.hd(revHalfs);
        let restHalfs = List.rev(List.tl(revHalfs));
        {
          completed: os.completed,
          halfOpen:
            restHalfs
            @ [
              {
                ...lastHalf,
                hoRightUnforms:
                  lastHalf.hoRightUnforms @ [unform],
              },
            ],
        };
      }
    | UShard(_) => {
        completed:
          opStateRollFromRight(os, None) @ [Unform(unform)],
        halfOpen: [],
      }
    }
  | Form(form) => opPushForm(os, None, [], form)
  };

let rec closePartialForm = (f: partialForm): closedForm =>
  switch (f) {
  | Head(token) => CHead(token)
  | PMatch(form, items, token) =>
    CMatch(closePartialForm(form), operatorize(items), token)
  }
and closeShardePartialForm =
    (f: sharded(partialForm)): sharded(closedForm) =>
  switch (f) {
  | Unform(u) => Unform(u)
  | Form(form) => Form(closePartialForm(form))
  }
and opPushes =
    (s: opState, fs: list(sharded(partialForm))): opState =>
  List.fold_left(
    (acc, f) => opPush(acc, closeShardePartialForm(f)),
    s,
    fs,
  )
and operatorize =
    (fs: list(sharded(partialForm))): list(sharded(openForm)) =>
  opStateRollFromRight(
    opPushes({completed: [], halfOpen: []}, fs),
    None,
  );

let parse = (tokens: list(ranged(token))): list(sharded(openForm)) =>
  operatorize(matchParse(tokens));
