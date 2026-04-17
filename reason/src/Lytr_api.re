open Grammar;
open Term;
open Lexer;
open Parser;
open Builder;
open Check;

let g = LytrGrammar.grammar;

/* === JS Map interop === */

type jsMap;

[@mel.new] external createJsMap: unit => jsMap = "Map";
[@mel.send] external jsMapSet: (jsMap, string, ml) => unit = "set";

let displayBinding = (name: string, ft: fullType): ml => {
  let (params, retType) = ft;
  let nameTerm = mkML(Identifier(name));
  let retML = embedOL(retType);
  let paramTerms =
    List.map(
      ((pname, ty)) => {
        let n =
          switch (pname) {
          | Some(s) => mkML(Identifier(s))
          | None => mkML(Hole(Synthesized))
          };
        let paramML = embedOL(ty);
        let t = mkML(Ap(mkML(Identifier(":")), [n, paramML]));
        {...t, meta: {...t.meta, parens: true}};
      },
      params,
    );
  switch (paramTerms) {
  | [] => mkML(Ap(mkML(Identifier(":")), [nameTerm, retML]))
  | _ =>
    let spine = mkML(Ap(nameTerm, paramTerms));
    mkML(Ap(mkML(Identifier(":")), [spine, retML]));
  };
};

let contextToJsMap = (ctx: context): jsMap => {
  let m = createJsMap();
  StringMap.iter(
    (k, v) =>
      switch (v) {
      | OL(Some(ft)) => jsMapSet(m, k, displayBinding(k, ft))
      | ML(ty) => jsMapSet(m, k, displayBinding(k, ([], mkOL(OLIdentifier(MLType.printType(ty))))))
      | Builtin(_) | SchemaBinding(_) | MetaLet(_, _) => ()
      | OL(None) => ()
      },
    ctx,
  );
  m;
};

/* === JS-facing types via mel.obj === */

type jsError;

[@mel.obj]
external makeJsError:
  (
    ~type_: [@mel.as "type"] string,
    ~message: string,
    ~from: int,
    ~to_: [@mel.as "to"] int,
  ) =>
  jsError =
  "";

type jsHoleInfo;

[@mel.obj]
external makeJsHoleInfo: (~goal: ml, ~context: jsMap) => jsHoleInfo = "";

type jsResult;

[@mel.obj]
external makeJsResult:
  (~errors: array(jsError), ~holes: array(array(Obj.t))) => jsResult =
  "";

/* === Pipeline === */

let processCode = (code: string): jsResult => {
  let statics = getStatics(build(parse(g, lex(g, code))));

  let errors =
    Array.of_list(
      List.map(
        (e: Error.error) =>
          makeJsError(~type_=e.type_, ~message=e.message, ~from=e.from, ~to_=e.to_),
        statics.errors,
      ),
    );

  let holes =
    Array.of_list(
      List.map(
        ((pos, info): (int, holeInfo)) =>
          [|
            Obj.repr(pos),
            Obj.repr(
              makeJsHoleInfo(~goal=info.goal, ~context=contextToJsMap(info.context)),
            ),
          |],
        statics.holes,
      ),
    );

  makeJsResult(~errors, ~holes);
};

let printTerm = (t: ml): string => Print.printML(t);

/* ML type checking */
type jsMLResult;

[@mel.obj]
external makeMLResult:
  (~ok: bool, ~error: string, ~from: int, ~to_: [@mel.as "to"] int) => jsMLResult =
  "";

let checkSchemaCode = (code: string): jsMLResult => {
  let ast = build(parse(g, lex(g, code)));
  let info = checkSchema(StringMap.empty, ast);
  switch (info.errors) {
  | [] => makeMLResult(~ok=true, ~error="", ~from=0, ~to_=0)
  | [{message, from, to_, _}, ..._] =>
    makeMLResult(~ok=false, ~error=message, ~from, ~to_)
  };
};

let parseAndPrint = (code: string): string =>
  Print.printML(build(parse(g, lex(g, code))));

let parseAndDebug = (code: string): string =>
  Print.debugML(build(parse(g, lex(g, code))));

/* ML evaluation */
type jsEvalResult;

[@mel.obj]
external makeEvalResult:
  (~ok: bool, ~value: string, ~error: string) => jsEvalResult = "";

let evalCode = (code: string): jsEvalResult => {
  let ast = build(parse(g, lex(g, code)));
  switch (Eval.evalExpr(Eval.StringMap.empty, ast)) {
  | Ok(v) => makeEvalResult(~ok=true, ~value=Print.printML(Eval.termOf(v)), ~error="")
  | Err(msg) => makeEvalResult(~ok=false, ~value="", ~error=msg)
  };
};

/* === Token data for CodeMirror tree === */

[@mel.send] external push: (array(int), int) => int = "push";

let lexToTokens = (code: string): array(int) => {
  let tokens = lex(g, code);
  let buf: array(int) = [||];

  List.iter(
    (rtok: Utils.ranged(token)) => {
      let nodeType =
        switch (rtok.value) {
        | Primary(TNamed(name)) =>
          let def = StringMap.find_opt(name, g.tokens);
          switch (def) {
          | Some({kind: Keyword(_), _}) => Some(1)
          | Some({kind: Symbol("(" | "["), _}) => Some(5)
          | Some({kind: Symbol(")" | "]"), _}) => Some(6)
          | Some({kind: Symbol(_), _}) => Some(4)
          | _ => None
          };
        | Primary(TAtom(Identifier(_))) => Some(2)
        | Primary(TAtom(StringLit(_))) => Some(8)
        | Primary(TAtom(Hole)) => Some(3)
        | Primary(BOF | EOF) => None
        | Secondary(Whitespace(_)) => None
        | Secondary(Unlexed(_)) => Some(7)
        };
      switch (nodeType) {
      | Some(nt) =>
        ignore(push(buf, nt));
        ignore(push(buf, rtok.start));
        ignore(push(buf, rtok.end_));
      | None => ()
      };
    },
    tokens,
  );

  buf;
};
