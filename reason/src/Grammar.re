open Utils;

type atom =
  | Hole
  | Identifier(string);

type primaryToken =
  | BOF
  | EOF
  | TOP
  | TCP
  | TAtom(atom)
  | TColon
  | TPostulate
  | TChecker
  | TConstruct
  | TEnd;

type secondaryToken =
  | Whitespace(string)
  | Unlexed(string);

type token =
  | Primary(primaryToken)
  | Secondary(secondaryToken);

type precedence =
  | Interior
  | Uninterested
  | Precedence(float);

let getPrecedence = (token: primaryToken): (precedence, precedence) =>
  switch (token) {
  | BOF => (Uninterested, Interior)
  | EOF => (Interior, Uninterested)
  | TOP => (Uninterested, Interior)
  | TCP => (Interior, Uninterested)
  | TAtom(_) => (Uninterested, Uninterested)
  | TColon => (Precedence(1.0), Precedence(1.1))
  | TPostulate => (Uninterested, Interior)
  | TChecker => (Uninterested, Interior)
  | TConstruct => (Uninterested, Interior)
  | TEnd => (Interior, Uninterested)
  };

type matchTokenResult =
  | Match
  | MatchMorph(primaryToken)
  | NoMatch;

let isBlockToken = (t: primaryToken): bool =>
  switch (t) {
  | TPostulate
  | TChecker
  | TConstruct => true
  | _ => false
  };

let matchToken = (t1: primaryToken, t2: primaryToken): matchTokenResult =>
  switch (t1, t2) {
  | (BOF, EOF) => Match
  | (TOP, TCP) => Match
  | _ when isBlockToken(t1) && isBlockToken(t2) => Match
  | _ when isBlockToken(t1) && t2 == TEnd => Match
  | _ => NoMatch
  };

let isValidStart = (token: primaryToken): bool => {
  let (leftPrec, _) = getPrecedence(token);
  leftPrec != Interior;
};

let isValidEnd = (token: ranged(primaryToken)): bool => {
  let (_, rightPrec) = getPrecedence(token.value);
  rightPrec != Interior;
};
