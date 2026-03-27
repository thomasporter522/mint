open Utils;
open Grammar;

let isWhitespace = (c: char): bool =>
  c == ' ' || c == '\t' || c == '\n' || c == '\r';

let isDigit = (c: char): bool => c >= '0' && c <= '9';

let isLetter = (c: char): bool =>
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');

let isAlphanum = (c: char): bool =>
  isLetter(c) || isDigit(c) || c == '_' || c == '-';

let lex = (s: string): list(ranged(token)) => {
  let len = String.length(s);
  let tokens = ref([]);
  let i = ref(0);

  while (i^ < len) {
    let start = i^;
    let c = s.[i^];

    if (isWhitespace(c)) {
      tokens := [
        {
          value: Secondary(Whitespace(String.make(1, c))),
          start,
          end_: i^ + 1,
        },
        ...tokens^,
      ];
      i := i^ + 1;
    } else if (isLetter(c)) {
      let j = ref(i^);
      while (j^ < len && isAlphanum(s.[j^])) {
        j := j^ + 1;
      };
      let idStr = String.sub(s, i^, j^ - i^);
      let primaryToken =
        switch (idStr) {
        | "postulate" => TPostulate
        | "checker" => TChecker
        | "construct" => TConstruct
        | "end" => TEnd
        | _ => TAtom(Identifier(idStr))
        };
      tokens := [
        {value: Primary(primaryToken), start: i^, end_: j^},
        ...tokens^,
      ];
      i := j^;
    } else {
      let singleCharToken =
        switch (c) {
        | '(' => Some(Primary(TOP))
        | ')' => Some(Primary(TCP))
        | '?' => Some(Primary(TAtom(Hole)))
        | ':' => Some(Primary(TColon))
        | _ => None
        };
      switch (singleCharToken) {
      | Some(tok) =>
        tokens := [
          {value: tok, start, end_: i^ + 1},
          ...tokens^,
        ];
        i := i^ + 1;
      | None =>
        tokens := [
          {
            value: Secondary(Unlexed(String.make(1, c))),
            start,
            end_: i^ + 1,
          },
          ...tokens^,
        ];
        i := i^ + 1;
      };
    };
  };

  List.rev(tokens^);
};
