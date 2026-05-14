open Term;
open Check;
open Decode;

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
        let t = mkML(Asc(n, paramML));
        {...t, meta: {...t.meta, parens: true}};
      },
      params,
    );
  switch (paramTerms) {
  | [] => mkML(Asc(nameTerm, retML))
  | _ =>
    let spine = mkML(Ap(nameTerm, paramTerms));
    mkML(Asc(spine, retML));
  };
};

let contextToJsMap = (ctx: context): jsMap => {
  let m = createJsMap();
  StringMap.iter(
    (k, v) =>
      switch (v) {
      | OL(Some(ft), _) => jsMapSet(m, k, displayBinding(k, ft))
      | ML(ty) => jsMapSet(m, k, displayBinding(k, ([], mkOL(OLIdentifier(MLType.printType(ty))))))
      | Builtin(_) | SchemaBinding(_) | CoerceBinding(_) | MetaLet(_, _) => ()
      | OL(None, _) => ()
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
  (
    ~errors: array(jsError),
    ~holes: array(array(Obj.t)),
    ~inlayHints: array(array(Obj.t)),
    ~definitions: array(array(int)),
    ~completeBlocks: array(array(int)),
  ) =>
  jsResult =
  "";

let resultOfStatics = (statics: staticInfo): jsResult => {
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
  /* Inlay hints carry ghost terms (already zonked at the decl boundary).
     Each entry surfaces both a label (collapsed to `…` when every ghost
     resolved, or the values rendering otherwise) and a tooltip (always
     the values rendering). Hovering the ellipsis shows the expansion. */
  let inlayHints =
    Array.of_list(
      List.map(
        ((pos, kind, ghosts): (int, Check.hintKind, list(ol))) =>
          [|
            Obj.repr(pos),
            Obj.repr(Check.renderHintLabel(kind, ghosts)),
            Obj.repr(Check.renderHintValues(ghosts)),
          |],
        statics.inlayHints,
      ),
    );
  let definitions =
    Array.of_list(
      List.map(
        ((useM, defM): (meta, meta)) =>
          [|useM.start, useM.end_, defM.start, defM.end_|],
        statics.definitions,
      ),
    );
  /* Emit each complete block's full source range. The bridge filters
     out blocks whose range overlaps any error (syntactic or semantic
     that the engine didn't catch per-decl). The extension anchors a ✓
     at the start (the block's keyword). */
  let completeBlocks =
    Array.of_list(
      List.map(
        (m: meta) => [|m.start, m.end_|],
        statics.completeBlocks,
      ),
    );
  makeJsResult(~errors, ~holes, ~inlayHints, ~definitions, ~completeBlocks);
};

/* === Pipeline entry points ===
   These accept the JS-encoded AST produced by web/src/frontend/builder.ts. */

let processProgramJs = (jsArr: array(jsObj)): jsResult => {
  let prog = decodeProgram(jsArr);
  let statics = checkProgram(StringMap.empty, prog);
  resultOfStatics(statics);
};

let printTerm = (t: ml): string => Print.printML(t);

let printProgramJs = (jsArr: array(jsObj)): string => {
  let prog = decodeProgram(jsArr);
  Print.printProgram(prog);
};

/* elaborate: take a parsed program, run elaboration, and return the
   printed elaborated source plus the errors. Used by the idempotence
   tests: elaborate(elaborate(p)) should match elaborate(p) on both
   the printed term and the errors. */
type jsElabResult;

[@mel.obj]
external makeJsElabResult:
  (~elaborated: string, ~errors: array(jsError)) => jsElabResult = "";

let elaborateProgramJs = (jsArr: array(jsObj)): jsElabResult => {
  let prog = decodeProgram(jsArr);
  let (elabProg, errs) = Check.elaborateProgram(StringMap.empty, prog);
  let errors =
    Array.of_list(
      List.map(
        (e: Error.error) =>
          makeJsError(~type_=e.type_, ~message=e.message, ~from=e.from, ~to_=e.to_),
        errs,
      ),
    );
  makeJsElabResult(~elaborated=Print.printProgram(elabProg), ~errors);
};

let printMLJs = (jsML: jsObj): string => {
  let ml = decodeML(jsML);
  Print.printML(ml);
};

/* ML schema check — takes a JS ML expression. */
type jsMLResult;

[@mel.obj]
external makeMLResult:
  (~ok: bool, ~error: string, ~from: int, ~to_: [@mel.as "to"] int) => jsMLResult =
  "";

let checkSchemaMLJs = (jsML: jsObj): jsMLResult => {
  let ast = decodeML(jsML);
  let info = checkSchema(StringMap.empty, ast);
  switch (info.errors) {
  | [] => makeMLResult(~ok=true, ~error="", ~from=0, ~to_=0)
  | [{message, from, to_, _}, ..._] =>
    makeMLResult(~ok=false, ~error=message, ~from, ~to_)
  };
};

/* ML evaluation — takes a JS ML expression. */
type jsEvalResult;

[@mel.obj]
external makeEvalResult:
  (~ok: bool, ~value: string, ~error: string) => jsEvalResult = "";

let evalMLJs = (jsML: jsObj): jsEvalResult => {
  let ast = decodeML(jsML);
  switch (Eval.evalExpr(Eval.StringMap.empty, ast)) {
  | Ok(v) => makeEvalResult(~ok=true, ~value=Print.printML(Eval.termOf(v)), ~error="")
  | Err(msg) => makeEvalResult(~ok=false, ~value="", ~error=msg)
  };
};
