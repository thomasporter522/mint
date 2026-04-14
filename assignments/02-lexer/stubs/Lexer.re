open Utils;
open Grammar;

let isWhitespace = c => c == ' ' || c == '\t' || c == '\n' || c == '\r';
let isDigit      = c => c >= '0' && c <= '9';
let isLetter     = c => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
let isAlphanum   = c => isLetter(c) || isDigit(c) || c == '_' || c == '-';

/* Tokenize a string according to the grammar's keyword and symbol maps.
   Returns tokens in source order with character offset positions.

   Token kinds:
   - Primary(TAtom(Identifier(s)))  — an identifier
   - Primary(TAtom(StringLit(s)))   — a string literal (content without quotes)
   - Primary(TAtom(Hole))           — a bare ?
   - Primary(TNamed(name))          — a keyword or symbol
   - Secondary(Whitespace(s))       — whitespace or comment
   - Secondary(Unlexed(s))          — unrecognized character

   Implementation strategy:
   1. Collect all symbol strings from g.symbolMap, sort longest first
   2. Walk through the string character by character
   3. At each position, try to match (in priority order):
      whitespace, line comment (--), string literal, identifier/keyword,
      hole (?), symbol, or fallback to unlexed
   4. Accumulate tokens in reverse, then List.rev at the end */
let lex = (g: grammar, s: string): list(ranged(token)) => {
  let len = String.length(s);
  let acc = ref([]);
  let emit = (tok, start, end_) => acc := [{value: tok, start, end_}, ...acc^];
  let i = ref(0);

  /* Sort symbols longest first for greedy matching */
  let symbols =
    StringMap.bindings(g.symbolMap)
    |> List.map(((sym, _name)) => sym)
    |> List.sort((a, b) => String.length(b) - String.length(a));

  while (i^ < len) {
    let start = i^;
    let c = s.[i^];

    /* TODO: handle each token kind in priority order:
       1. Whitespace
       2. Line comment (--)
       3. String literal ("...")
       4. Identifier/keyword (starts with letter)
       5. Hole (? or ?name)
       6. Symbol (greedy match from symbols list)
       7. Unlexed fallback */
    failwith("TODO");
  };

  List.rev(acc^);
};
