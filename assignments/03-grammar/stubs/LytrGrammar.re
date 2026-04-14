open Grammar;

let blockKeywords = ["postulate", "meta", "construct"];

/* Define the Lytr language grammar.

   Build up the grammar by piping through Grammar.re API functions:
   addToken, addKeyword, addSymbol, addInfix, addParens, addBlock, addMatch

   Sections to implement:

   1. BRACKETS WITH COMMA MORPHING
      - ( ) [ ] and , tokens
      - MatchPair for ( ) and [ ]
      - Comma morphing: commas inside parens become ",p", inside brackets become ",l"
        Use MatchPairMorph("(", ",", ",p") so a comma matched after ( becomes ,p
        Then MatchPairMorph(",p", ",", ",p") so subsequent commas also morph
        And MatchPair(",p", ")") to close the morphed sequence
        Same pattern for [ ] with ,l
      - The ,p and ,l tokens have kind AtomIdent (they're virtual, never lexed)

   2. INFIX OPERATORS
      Use addInfix(name, ~symbol, ~left, ~right, g) for each:
      - "="  symbol "="  left 0.2  right 0.3
      - ":"  symbol ":"  left 1.0  right 1.1
      - "->" symbol "->" left 2.0  right 1.9  (right-associative: left > right)
      - "!=" symbol "!=" left 4.0  right 4.1
      - "==" symbol "==" left 4.0  right 4.1
      - "&&" symbol "&&" left 5.0  right 5.1
      - "||" symbol "||" left 6.0  right 6.1

   3. MATCH/WITH/PIPE/ARROW AND END
      - "end" keyword: leftPrec Interior, rightPrec Uninterested
      - "match" keyword: leftPrec Uninterested, rightPrec Interior
      - "with" keyword: leftPrec Interior, rightPrec Interior
      - "|" symbol: leftPrec Interior, rightPrec Interior
      - "=>" symbol: leftPrec Interior, rightPrec Precedence(0.5)
      Match rules:
      - MatchPair("match", "with")
      - MatchPair("with", "|") and MatchPair("with", "end")
      - MatchPair("|", "=>")
      - MatchPair("=>", "|") and MatchPair("=>", "end")

   4. FUN/ARROW MORPH
      - "fun" keyword: leftPrec Uninterested, rightPrec Interior
      - "=>f" token with kind AtomIdent: leftPrec Interior, rightPrec Precedence(0.5)
      - MatchPairMorph("fun", "=>", "=>f") — morphs => to =>f inside fun
        This prevents fun's arrow from matching end (unlike match branch arrows)

   5. IF/THEN/ELSE
      - "if" keyword: leftPrec Uninterested, rightPrec Interior
      - "then" keyword: leftPrec Interior, rightPrec Interior
      - "else" keyword: leftPrec Interior, rightPrec Interior
      Match rules: if->then, then->else, else->end

   6. LET/IN
      - "let" keyword: leftPrec Uninterested, rightPrec Interior
      - "in" keyword: leftPrec Interior, rightPrec Precedence(0.1)
      Match rule: let->in

   7. ATOM KEYWORDS AND SYMBOLS
      - "schema" keyword: Uninterested/Uninterested (atom, no children)
      - "_" symbol: Uninterested/Uninterested
      - "..." symbol: Uninterested/Uninterested

   8. CONSTRUCT/BY
      - "by" keyword: leftPrec Interior, rightPrec Interior
      - MatchPair("construct", "by")

   9. BLOCK KEYWORDS
      For each keyword in blockKeywords:
      - addBlock(kw, ~close="end", g) — adds the keyword token + MatchBlockEnd
      - MatchBlockBlock(kw, other) for every keyword in blockKeywords
        (this lets postulate...meta...construct...end chains work)

   10. BY INHERITS BLOCK BEHAVIOR
       - MatchBlockEnd("by", "end")
       - MatchBlockBlock("by", kw) for each block keyword
         (because "construct...by" means by takes over construct's role) */
let grammar = {
  failwith("TODO");
};
