open Utils;
open Grammar;

let isWhitespace = c => c == ' ' || c == '\t' || c == '\n' || c == '\r';
let isDigit      = c => c >= '0' && c <= '9';
let isLetter     = c => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
let isAlphanum   = c => isLetter(c) || isDigit(c) || c == '_' || c == '-';

let keywordOrIdent =
  fun
  | "postulate" => TPostulate
  | "schema"   => TSchema
  | "construct" => TConstruct
  | "end"       => TEnd
  | s           => TAtom(Identifier(s));

let singleCharToken =
  fun
  | '(' => Some(Primary(TOP))
  | ')' => Some(Primary(TCP))
  | '?' => Some(Primary(TAtom(Hole)))
  | ':' => Some(Primary(TColon))
  | _   => None;

let lex = (s: string): list(ranged(token)) => {
  let len = String.length(s);
  let acc = ref([]);
  let emit = (tok, start, end_) => acc := [{value: tok, start, end_}, ...acc^];
  let i = ref(0);

  while (i^ < len) {
    let start = i^;
    let c = s.[i^];

    if (isWhitespace(c)) {
      emit(Secondary(Whitespace(String.make(1, c))), start, start + 1);
      i := i^ + 1;
    } else if (isLetter(c)) {
      let j = ref(i^);
      while (j^ < len && isAlphanum(s.[j^])) {
        j := j^ + 1;
      };
      emit(Primary(keywordOrIdent(String.sub(s, i^, j^ - i^))), i^, j^);
      i := j^;
    } else {
      switch (singleCharToken(c)) {
      | Some(tok) => emit(tok, start, start + 1)
      | None => emit(Secondary(Unlexed(String.make(1, c))), start, start + 1)
      };
      i := i^ + 1;
    };
  };

  List.rev(acc^);
};
