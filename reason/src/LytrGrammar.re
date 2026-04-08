open Grammar;

/* The lytr language grammar, built from primitives */

let blockKeywords = ["postulate", "schema", "construct"];

let grammar = {
  let g =
    empty
    /* Brackets */
    |> addParens("(", ")")
    |> addParens("[", "]")
    /* Infix operators, lowest precedence first */
    |> addInfix("=",  ~symbol="=",  ~left=0.2, ~right=0.3)
    |> addInfix(":",  ~symbol=":",  ~left=1.0, ~right=1.1)
    |> addInfix("->", ~symbol="->", ~left=2.0, ~right=1.9) /* right-assoc */
    |> addInfix(",",  ~symbol=",",  ~left=3.0, ~right=3.1)
    |> addInfix("!=", ~symbol="!=", ~left=4.0, ~right=4.1)
    |> addInfix("==", ~symbol="==", ~left=4.0, ~right=4.1)
    |> addInfix("&&", ~symbol="&&", ~left=5.0, ~right=5.1)
    |> addInfix("||", ~symbol="||", ~left=6.0, ~right=6.1)
    /* Block end */
    |> addToken("end",   {kind: Keyword("end"),   leftPrec: Interior,     rightPrec: Uninterested})
    /* match...with...|...=>...|...=>...end chain */
    |> addToken("match", {kind: Keyword("match"), leftPrec: Uninterested, rightPrec: Interior})
    |> addToken("with",  {kind: Keyword("with"),  leftPrec: Interior,     rightPrec: Interior})
    |> addToken("|",     {kind: Symbol("|"),       leftPrec: Interior,     rightPrec: Interior})
    |> addToken("=>",    {kind: Symbol("=>"),      leftPrec: Interior,     rightPrec: Precedence(0.5)})
    |> addMatch(MatchPair("match", "with"))
    |> addMatch(MatchPair("with", "|"))
    |> addMatch(MatchPair("|", "=>"))
    |> addMatch(MatchPair("=>", "|"))
    |> addMatch(MatchPair("=>", "end"))
    /* if/then/else as atom keywords */
    |> addToken("if",    {kind: Keyword("if"),    leftPrec: Uninterested, rightPrec: Uninterested})
    |> addToken("then",  {kind: Keyword("then"),  leftPrec: Uninterested, rightPrec: Uninterested})
    |> addToken("else",  {kind: Keyword("else"),  leftPrec: Uninterested, rightPrec: Uninterested})
    /* fun...=> matched pair */
    |> addToken("fun",   {kind: Keyword("fun"),   leftPrec: Uninterested, rightPrec: Interior})
    |> addMatch(MatchPair("fun", "=>"))
    |> addToken("let",   {kind: Keyword("let"),   leftPrec: Uninterested, rightPrec: Uninterested})
    |> addToken("in",    {kind: Keyword("in"),    leftPrec: Uninterested, rightPrec: Uninterested})
    /* Wildcard */
    |> addToken("_",     {kind: Symbol("_"),      leftPrec: Uninterested, rightPrec: Uninterested});

  /* Add block keywords and their match rules */
  let g =
    List.fold_left(
      (g, kw) => {
        let g = addBlock(kw, ~close="end", g);
        /* Blocks also match each other (e.g. postulate...schema nests) */
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
