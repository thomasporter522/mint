open Grammar;

let blockKeywords = ["postulate", "schema", "construct"];

let grammar = {
  let g =
    empty
    /* Brackets with comma morphing to prevent (a, b] style mismatches */
    |> addToken("(",   {kind: Symbol("("),  leftPrec: Uninterested, rightPrec: Interior})
    |> addToken(")",   {kind: Symbol(")"),  leftPrec: Interior,     rightPrec: Uninterested})
    |> addToken("[",   {kind: Symbol("["),  leftPrec: Uninterested, rightPrec: Interior})
    |> addToken("]",   {kind: Symbol("]"),  leftPrec: Interior,     rightPrec: Uninterested})
    |> addToken(",",   {kind: Symbol(","),  leftPrec: Interior,     rightPrec: Interior})
    |> addToken(",p",  {kind: AtomIdent,     leftPrec: Interior,     rightPrec: Interior})  /* paren comma — created by morph only */
    |> addToken(",l",  {kind: AtomIdent,     leftPrec: Interior,     rightPrec: Interior})  /* list comma — created by morph only */
    |> addMatch(MatchPair("(", ")"))
    |> addMatch(MatchPairMorph("(", ",", ",p"))
    |> addMatch(MatchPairMorph(",p", ",", ",p"))
    |> addMatch(MatchPair(",p", ")"))
    |> addMatch(MatchPair("[", "]"))
    |> addMatch(MatchPairMorph("[", ",", ",l"))
    |> addMatch(MatchPairMorph(",l", ",", ",l"))
    |> addMatch(MatchPair(",l", "]"))
    /* Infix operators */
    |> addInfix("=",  ~symbol="=",  ~left=0.2, ~right=0.3)
    |> addInfix(":",  ~symbol=":",  ~left=1.0, ~right=1.1)
    |> addInfix("->", ~symbol="->", ~left=2.0, ~right=1.9) /* right-assoc */
    |> addInfix("!=", ~symbol="!=", ~left=4.0, ~right=4.1)
    |> addInfix("==", ~symbol="==", ~left=4.0, ~right=4.1)
    |> addInfix("&&", ~symbol="&&", ~left=5.0, ~right=5.1)
    |> addInfix("||", ~symbol="||", ~left=6.0, ~right=6.1)
    /* Block end */
    |> addToken("end", {kind: Keyword("end"), leftPrec: Interior, rightPrec: Uninterested})
    /* match...with...|...=>...|...=>...end */
    |> addToken("match", {kind: Keyword("match"), leftPrec: Uninterested, rightPrec: Interior})
    |> addToken("with",  {kind: Keyword("with"),  leftPrec: Interior,     rightPrec: Interior})
    |> addToken("|",     {kind: Symbol("|"),       leftPrec: Interior,     rightPrec: Interior})
    |> addToken("=>",    {kind: Symbol("=>"),      leftPrec: Interior,     rightPrec: Precedence(0.5)})
    |> addMatch(MatchPair("match", "with"))
    |> addMatch(MatchPair("with", "|"))
    |> addMatch(MatchPair("|", "=>"))
    |> addMatch(MatchPair("=>", "|"))
    |> addMatch(MatchPair("=>", "end"))
    /* fun...=> */
    |> addToken("fun", {kind: Keyword("fun"), leftPrec: Uninterested, rightPrec: Interior})
    |> addMatch(MatchPair("fun", "=>"))
    /* if...then...else...end */
    |> addToken("if",   {kind: Keyword("if"),   leftPrec: Uninterested, rightPrec: Interior})
    |> addToken("then", {kind: Keyword("then"), leftPrec: Interior,     rightPrec: Interior})
    |> addToken("else", {kind: Keyword("else"), leftPrec: Interior,     rightPrec: Interior})
    |> addMatch(MatchPair("if", "then"))
    |> addMatch(MatchPair("then", "else"))
    |> addMatch(MatchPair("else", "end"))
    /* let...in — matched pair, body after in needs parens */
    |> addToken("let", {kind: Keyword("let"), leftPrec: Uninterested, rightPrec: Interior})
    |> addToken("in",  {kind: Keyword("in"),  leftPrec: Interior,     rightPrec: Precedence(0.1)})
    |> addMatch(MatchPair("let", "in"))
    |> addToken("_",   {kind: Symbol("_"),    leftPrec: Uninterested, rightPrec: Uninterested});

  /* Block keywords and their match rules */
  let g =
    List.fold_left(
      (g, kw) => {
        let g = addBlock(kw, ~close="end", g);
        List.fold_left(
          (g, other) => addMatch(MatchBlockBlock(kw, other), g),
          g,
          blockKeywords,
        );
      },
      g,
      blockKeywords,
    );

  g;
};
