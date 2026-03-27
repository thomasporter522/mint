/* Main API module - exports functions for TypeScript consumption */

open Term;
open Lexer;
open Parser;
open Builder;
open Check;

/* === JS Map interop === */

type jsMap;

[@mel.new] external createJsMap: unit => jsMap = "Map";
[@mel.send] external jsMapSet: (jsMap, string, term) => unit = "set";

let contextToJsMap = (ctx: context): jsMap => {
  let m = createJsMap();
  StringMap.iter(
    (k, v) =>
      switch (v) {
      | Some((_, retType)) => jsMapSet(m, k, retType)
      | None => ()
      },
    ctx,
  );
  m;
};

/* === Error type for JS output === */

type jsError;

[@mel.obj]
external makeJsError:
  (
    ~type_: [@mel.as "type"] string,
    ~message: string,
    ~from: int,
    ~to_: [@mel.as "to"] int
  ) =>
  jsError =
  "";

let errorToJs = (e: Error.error): jsError =>
  makeJsError(~type_=e.type_, ~message=e.message, ~from=e.from, ~to_=e.to_);

/* === Hole info === */

type jsHoleInfo;

[@mel.obj]
external makeJsHoleInfo: (~goal: term, ~context: jsMap) => jsHoleInfo = "";

/* === Result type === */

type jsResult;

[@mel.obj]
external makeJsResult:
  (~errors: array(jsError), ~holes: array(array(Obj.t))) => jsResult =
  "";

/* The combined pipeline: code string -> {errors, holes} */
let processCode = (code: string): jsResult => {
  let tokens = lex(code);
  let parsed = parse(tokens);
  let ast = build(parsed);
  let statics = getStatics(ast);

  let errors = Array.of_list(List.map(errorToJs, statics.errors));

  let holes =
    Array.of_list(
      List.map(
        ((pos, info): (int, holeInfo)) => {
          let holeInfo =
            makeJsHoleInfo(
              ~goal=info.goal,
              ~context=contextToJsMap(info.context),
            );
          [|Obj.repr(pos), Obj.repr(holeInfo)|];
        },
        statics.holes,
      ),
    );

  makeJsResult(~errors, ~holes);
};

/* printTerm operates on opaque ML terms */
let printTerm = (t: term): string => Print.printTerm(t);
