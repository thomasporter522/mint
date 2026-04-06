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
  | TSchema
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
  | BOF        => (Uninterested, Interior)
  | EOF        => (Interior,     Uninterested)
  | TOP        => (Uninterested, Interior)
  | TCP        => (Interior,     Uninterested)
  | TAtom(_)   => (Uninterested, Uninterested)
  | TColon     => (Precedence(1.0), Precedence(1.1))
  | TPostulate => (Uninterested, Interior)
  | TSchema   => (Uninterested, Interior)
  | TConstruct => (Uninterested, Interior)
  | TEnd       => (Interior,     Uninterested)
  };

let leftPrec  = t => fst(getPrecedence(t));
let rightPrec = t => snd(getPrecedence(t));

type matchTokenResult =
  | Match
  | MatchMorph(primaryToken)
  | NoMatch;

let isBlockToken =
  fun
  | TPostulate | TSchema | TConstruct => true
  | _ => false;

let matchToken = (t1: primaryToken, t2: primaryToken): matchTokenResult =>
  switch (t1, t2) {
  | (BOF, EOF) => Match
  | (TOP, TCP) => Match
  | _ when isBlockToken(t1) && isBlockToken(t2) => Match
  | _ when isBlockToken(t1) && t2 == TEnd => Match
  | _ => NoMatch
  };

let isValidStart = t => leftPrec(t) != Interior;

let isValidEnd = (t: ranged(primaryToken)) => rightPrec(t.value) != Interior;

// Alternate way to express the start, end, and matching information

// type languageExpression = 
//   | Token(primaryToken)
//   | Sequence(list(languageExpression))
//   | Sum(list(languageExpression))
//   | Star(languageExpression)

// let matchingLanguage : languageExpression = 
//   Sum([
//     Sequence([Token(BOF), Token(EOF)]),
//     Sequence([Token(TOP), Token(TCP)]),
//     // how to express Atoms or things with params?
//     // Token(TAtom(...)),
//   ])