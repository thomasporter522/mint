open Utils;

/* ================================================================
   Grammar specification as data.

   Tokens are identified by strings. The grammar is a collection of:
   - Token definitions: how to lex them, their precedence
   - Matching rules: which tokens pair up (brackets, blocks)
   - Builder rules: how parse tree shapes become AST nodes

   The parser engine (Parser.re) is generic over any grammar.
   ================================================================ */

/* --- Token kinds for lexing --- */

type tokenKind =
  | Keyword(string)          /* alphabetic, e.g. "postulate" */
  | Symbol(string)           /* punctuation, e.g. ":" or "->" */
  | AtomHole                 /* the ? character */
  | AtomIdent                /* any identifier not matching a keyword */;

/* --- Precedence --- */

type precedence =
  | Interior
  | Uninterested
  | Precedence(float);

/* --- A token in the grammar --- */

type tokenDef = {
  kind: tokenKind,
  leftPrec: precedence,
  rightPrec: precedence,
};

/* --- Matching rules --- */

type matchRule =
  | MatchPair(string, string)              /* e.g. ("(", ")") */
  | MatchPairMorph(string, string, string) /* e.g. ("(", ",", ",p") — match and morph right token */
  | MatchBlockEnd(string, string)          /* e.g. ("postulate", "end") */
  | MatchBlockBlock(string, string);       /* e.g. ("postulate", "schema") */

/* --- The grammar object --- */

module StringMap = Map.Make(String);

type grammar = {
  tokens: StringMap.t(tokenDef),
  matchRules: list(matchRule),
  /* Reverse lookups built from tokens */
  keywordMap: StringMap.t(string),     /* "postulate" -> token name */
  symbolMap: StringMap.t(string),      /* ":" -> token name */
};

let empty: grammar = {
  tokens: StringMap.empty,
  matchRules: [],
  keywordMap: StringMap.empty,
  symbolMap: StringMap.empty,
};

/* --- Adding tokens --- */

let addToken = (name: string, def: tokenDef, g: grammar): grammar => {
  let keywordMap =
    switch (def.kind) {
    | Keyword(kw) => StringMap.add(kw, name, g.keywordMap)
    | _ => g.keywordMap
    };
  let symbolMap =
    switch (def.kind) {
    | Symbol(sym) => StringMap.add(sym, name, g.symbolMap)
    | _ => g.symbolMap
    };
  {
    ...g,
    tokens: StringMap.add(name, def, g.tokens),
    keywordMap,
    symbolMap,
  };
};

/* --- Adding match rules --- */

let addMatch = (rule: matchRule, g: grammar): grammar => {
  {...g, matchRules: [rule, ...g.matchRules]};
};

/* --- Convenience builders --- */

let addKeyword = (name: string, ~leftPrec, ~rightPrec, g: grammar): grammar =>
  addToken(name, {kind: Keyword(name), leftPrec, rightPrec}, g);

let addSymbol = (name: string, ~symbol, ~leftPrec, ~rightPrec, g: grammar): grammar =>
  addToken(name, {kind: Symbol(symbol), leftPrec, rightPrec}, g);

let addInfix = (name: string, ~symbol, ~left: float, ~right: float, g: grammar): grammar =>
  addSymbol(name, ~symbol, ~leftPrec=Precedence(left), ~rightPrec=Precedence(right), g);

let addParens = (open_: string, close: string, g: grammar): grammar => {
  let g = addToken(open_, {kind: Symbol(open_), leftPrec: Uninterested, rightPrec: Interior}, g);
  let g = addToken(close, {kind: Symbol(close), leftPrec: Interior, rightPrec: Uninterested}, g);
  addMatch(MatchPair(open_, close), g);
};

let addBlock = (keyword: string, ~close: string, g: grammar): grammar => {
  let g = addKeyword(keyword, ~leftPrec=Uninterested, ~rightPrec=Interior, g);
  addMatch(MatchBlockEnd(keyword, close), g);
};

/* --- Runtime token representation (what the lexer/parser use) --- */

type atom =
  | Hole
  | Identifier(string)
  | StringLit(string);

type primaryToken =
  | BOF
  | EOF
  | TAtom(atom)
  | TNamed(string);   /* all grammar-defined tokens identified by name */

type secondaryToken =
  | Whitespace(string)
  | Unlexed(string);

type token =
  | Primary(primaryToken)
  | Secondary(secondaryToken);

/* --- Grammar queries (used by parser) --- */

let getPrecedence = (g: grammar, t: primaryToken): (precedence, precedence) =>
  switch (t) {
  | BOF => (Uninterested, Interior)
  | EOF => (Interior, Uninterested)
  | TAtom(_) => (Uninterested, Uninterested)
  | TNamed(name) =>
    switch (StringMap.find_opt(name, g.tokens)) {
    | Some(def) => (def.leftPrec, def.rightPrec)
    | None => (Uninterested, Uninterested)
    }
  };

let leftPrec = (g, t) => fst(getPrecedence(g, t));
let rightPrec = (g, t) => snd(getPrecedence(g, t));

type matchTokenResult =
  | Match
  | MatchMorph(primaryToken)
  | NoMatch;

let matchToken = (g: grammar, t1: primaryToken, t2: primaryToken): matchTokenResult => {
  let name1 =
    switch (t1) {
    | TNamed(n) => Some(n)
    | _ => None
    };
  let name2 =
    switch (t2) {
    | TNamed(n) => Some(n)
    | _ => None
    };
  switch (name1, name2) {
  | (Some(n1), Some(n2)) =>
    let result = ref(NoMatch);
    List.iter(
      rule =>
        if (result^ == NoMatch) {
          switch (rule) {
          | MatchPair(a, b) =>
            if (n1 == a && n2 == b) { result := Match }
          | MatchPairMorph(a, b, morphTo) =>
            if (n1 == a && n2 == b) { result := MatchMorph(TNamed(morphTo)) }
          | MatchBlockEnd(a, b) =>
            if (n1 == a && n2 == b) { result := Match }
          | MatchBlockBlock(a, b) =>
            if (n1 == a && n2 == b) { result := Match }
          };
        },
      g.matchRules,
    );
    result^;
  | _ =>
    /* BOF/EOF matching */
    switch (t1, t2) {
    | (BOF, EOF) => Match
    | _ => NoMatch
    }
  };
};

let isValidStart = (g, t) => leftPrec(g, t) != Interior;
let isValidEnd = (g, t: ranged(primaryToken)) => rightPrec(g, t.value) != Interior;
