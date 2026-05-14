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
    ~autoHoles: array(array(Obj.t)),
    ~inlayHints: array(array(Obj.t)),
    ~definitions: array(array(int)),
    ~completeBlocks: array(array(int)),
    ~allBlocks: array(array(int)),
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
  let holeToJs = ((pos, info): (int, holeInfo)) =>
    [|
      Obj.repr(pos),
      Obj.repr(
        makeJsHoleInfo(~goal=info.goal, ~context=contextToJsMap(info.context)),
      ),
    |];
  let holes = Array.of_list(List.map(holeToJs, statics.holes));
  let autoHoles = Array.of_list(List.map(holeToJs, statics.autoHoles));
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
  let allBlocks =
    Array.of_list(
      List.map(
        (m: meta) => [|m.start, m.end_|],
        statics.allBlocks,
      ),
    );
  makeJsResult(~errors, ~holes, ~autoHoles, ~inlayHints, ~definitions, ~completeBlocks, ~allBlocks);
};

/* === Pipeline entry points ===
   These accept the JS-encoded AST produced by web/src/frontend/builder.ts. */

let processProgramJs = (jsArr: array(jsObj)): jsResult => {
  let prog = decodeProgram(jsArr);
  let statics = checkProgram(StringMap.empty, prog);
  resultOfStatics(statics);
};

let printTerm = (t: ml): string => Print.printML(t);

/* Focused verification of a Canonical candidate. Called by the bridge
   AFTER `processProgramJs` has populated `autoHoleContextsRef`. The
   candidate is decoded as an OL term and checked at the saved
   (context, expected) for the auto-hole at `offset`. Returns the list
   of errors (empty = candidate accepted). */
let verifyAutoCandidateJs = (offset: int, candidateJs: jsObj): array(jsError) => {
  let candidate = Decode.decodeOL(candidateJs);
  let errs = Check.verifyAutoCandidate(offset, candidate);
  Array.of_list(
    List.map(
      (e: Error.error) =>
        makeJsError(~type_=e.type_, ~message=e.message, ~from=e.from, ~to_=e.to_),
      errs,
    ),
  );
};

/* Build a Reason context (StringMap of bindings) from a meta-level
   signature list, the same shape `canonical` and schemas receive. */
let contextOfSignatureML = (ctxMl: ml): Check.context =>
  switch (ctxMl.value) {
  | List(entries) =>
    List.fold_left(
      (acc, entry: ml) =>
        switch (entry.value) {
        | Tuple([nameT, paramsT, retT]) =>
          let name =
            switch (nameT.value) {
            | Identifier(n) => n
            | _ => "_"
            };
          let params: list((option(string), ol)) =
            switch (paramsT.value) {
            | List(ps) =>
              List.map(
                (p: ml) =>
                  switch (p.value) {
                  | Tuple([pn, pty]) =>
                    let pname =
                      switch (pn.value) {
                      | Identifier(s) => Some(s)
                      | _ => None
                      };
                    (pname, Check.mlToOL(pty));
                  | _ => (None, Check.olHole)
                  },
                ps,
              )
            | _ => []
            };
          let retOL = Check.mlToOL(retT);
          StringMap.add(name, Check.OL(Some((params, retOL)), None), acc);
        | _ => acc
        },
      StringMap.empty,
      entries,
    )
  | _ => StringMap.empty
  };

/* Verify a candidate against a context expressed as a signature list
   (same shape `canonical` receives meta-side). Used by the bridge's
   `canonical` callback to verify what the solver returns. */
let verifyCandidateInContextJs =
    (ctxJs: jsObj, expectedJs: jsObj, candidateJs: jsObj): array(jsError) => {
  let ctx = contextOfSignatureML(Decode.decodeML(ctxJs));
  let expected = Decode.decodeOL(expectedJs);
  let candidate = Decode.decodeOL(candidateJs);
  let (info, _) =
    Check.checkOLTerm(
      Check.emptyElabState,
      ctx,
      Check.Expression(Some(expected)),
      candidate,
    );
  Array.of_list(
    List.map(
      (e: Error.error) =>
        makeJsError(~type_=e.type_, ~message=e.message, ~from=e.from, ~to_=e.to_),
      info.errors,
    ),
  );
};

/* Bridge registration: install a JS function as the Canonical solver
   callback that Eval invokes when it encounters `canonical(ctx, goal)`.
   The callback receives the evaluated ctx and goal as ml ASTs and
   returns an ml AST (`Ok candidate` or `Error msg`). */
let setCanonicalCallbackJs = (fn: (jsObj, jsObj) => jsObj): unit =>
  Eval.setCanonicalCallback((ctx, goal) =>
    Decode.decodeML(fn(Obj.magic(ctx), Obj.magic(goal)))
  );

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
