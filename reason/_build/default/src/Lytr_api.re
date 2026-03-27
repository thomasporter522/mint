open Term;
open Lexer;
open Parser;
open Builder;
open Check;

/* === JS Map interop === */

type jsMap;

[@mel.new] external createJsMap: unit => jsMap = "Map";
[@mel.send] external jsMapSet: (jsMap, string, term) => unit = "set";

let displayTerm = (name: string, ft: fullType): term => {
  let (params, retType) = ft;
  let nameTerm = mk(Identifier(name));
  switch (params) {
  | [] => mk(Asc(nameTerm, retType))
  | _ =>
    let paramTerms =
      List.map(
        ((pname, ty)) => {
          let n =
            switch (pname) {
            | Some(s) => mk(Identifier(s))
            | None => mk(Hole(true))
            };
          let asc = mk(Asc(n, ty));
          {...asc, meta: {...asc.meta, parens: true}};
        },
        params,
      );
    let spine =
      switch (paramTerms) {
      | [] => nameTerm
      | [first, ...rest] => mk(Ap(nameTerm, [first, ...rest]))
      };
    mk(Asc(spine, retType));
  };
};

let contextToJsMap = (ctx: context): jsMap => {
  let m = createJsMap();
  StringMap.iter(
    (k, v) =>
      switch (v) {
      | Some(ft) => jsMapSet(m, k, displayTerm(k, ft))
      | None => ()
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
external makeJsHoleInfo: (~goal: term, ~context: jsMap) => jsHoleInfo = "";

type jsResult;

[@mel.obj]
external makeJsResult:
  (~errors: array(jsError), ~holes: array(array(Obj.t))) => jsResult =
  "";

/* === Pipeline === */

let processCode = (code: string): jsResult => {
  let statics = getStatics(build(parse(lex(code))));

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

let printTerm = (t: term): string => Print.printTerm(t);
