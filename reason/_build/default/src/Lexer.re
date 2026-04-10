open Utils;
open Grammar;

let isWhitespace = c => c == ' ' || c == '\t' || c == '\n' || c == '\r';
let isDigit      = c => c >= '0' && c <= '9';
let isLetter     = c => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
let isAlphanum   = c => isLetter(c) || isDigit(c) || c == '_' || c == '-';

let lex = (g: grammar, s: string): list(ranged(token)) => {
  let len = String.length(s);
  let acc = ref([]);
  let emit = (tok, start, end_) => acc := [{value: tok, start, end_}, ...acc^];
  let i = ref(0);

  /* Collect all symbol strings sorted longest first for greedy matching */
  let symbols =
    StringMap.bindings(g.symbolMap)
    |> List.map(((sym, _name)) => sym)
    |> List.sort((a, b) => String.length(b) - String.length(a));

  while (i^ < len) {
    let start = i^;
    let c = s.[i^];

    if (isWhitespace(c)) {
      emit(Secondary(Whitespace(String.make(1, c))), start, start + 1);
      i := i^ + 1;
    } else if (c == '-' && i^ + 1 < len && s.[i^ + 1] == '-') {
      /* Line comment: -- to end of line */
      let j = ref(i^ + 2);
      while (j^ < len && s.[j^] != '\n') {
        j := j^ + 1;
      };
      emit(Secondary(Whitespace(String.sub(s, start, j^ - start))), start, j^);
      i := j^;
    } else if (c == '"') {
      /* String literal */
      let j = ref(i^ + 1);
      while (j^ < len && s.[j^] != '"') {
        j := j^ + 1;
      };
      let content =
        if (j^ < len) {
          j := j^ + 1; /* consume closing quote */
          String.sub(s, i^ + 1, j^ - i^ - 2);
        } else {
          String.sub(s, i^ + 1, j^ - i^ - 1); /* unclosed */
        };
      emit(Primary(TAtom(StringLit(content))), start, j^);
      i := j^;
    } else if (isLetter(c)) {
      let j = ref(i^);
      while (j^ < len && isAlphanum(s.[j^])) {
        j := j^ + 1;
      };
      let word = String.sub(s, i^, j^ - i^);
      let tok =
        switch (StringMap.find_opt(word, g.keywordMap)) {
        | Some(name) => Primary(TNamed(name))
        | None => Primary(TAtom(Identifier(word)))
        };
      emit(tok, i^, j^);
      i := j^;
    } else if (c == '?') {
      /* ? followed by identifier = meta-variable, bare ? = hole */
      if (i^ + 1 < len && isLetter(s.[i^ + 1])) {
        let j = ref(i^ + 1);
        while (j^ < len && isAlphanum(s.[j^])) {
          j := j^ + 1;
        };
        let name = String.sub(s, i^ + 1, j^ - i^ - 1);
        emit(Primary(TAtom(Identifier("?" ++ name))), start, j^);
        i := j^;
      } else {
        emit(Primary(TAtom(Hole)), start, start + 1);
        i := i^ + 1;
      };
    } else {
      /* Try to match a symbol (greedy, longest first) */
      let matched = ref(false);
      List.iter(
        sym => {
          if (!matched^) {
            let symLen = String.length(sym);
            if (start + symLen <= len
                && String.sub(s, start, symLen) == sym) {
              switch (StringMap.find_opt(sym, g.symbolMap)) {
              | Some(name) =>
                emit(Primary(TNamed(name)), start, start + symLen);
                i := start + symLen;
                matched := true;
              | None => ()
              };
            };
          }
        },
        symbols,
      );
      if (!matched^) {
        emit(Secondary(Unlexed(String.make(1, c))), start, start + 1);
        i := i^ + 1;
      };
    };
  };

  List.rev(acc^);
};
