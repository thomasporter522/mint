/* Decode the JS AST produced by web/src/frontend/builder.ts into the native
   OCaml AST defined in Term.re. Field names and `kind` discriminators
   match ast.ts exactly — keep them in sync. */

open Term;

/* === JS interop === */

type jsObj;

[@mel.send] external getString: (jsObj, string) => string = "get";
/* Use Js.Dict-style accessors on the dynamic JS object. Unsafe casts
   are fine here — the contract is enforced by ast.ts on the TS side. */

external _coerce: 'a => jsObj = "%identity";
external _untag: jsObj => Obj.t = "%identity";

[@mel.get_index] external _str: (jsObj, string) => string = "";
[@mel.get_index] external _strOpt: (jsObj, string) => Js.Nullable.t(string) = "";
[@mel.get_index] external _int: (jsObj, string) => int = "";
[@mel.get_index] external _bool: (jsObj, string) => bool = "";
[@mel.get_index] external _obj: (jsObj, string) => jsObj = "";
[@mel.get_index] external _objOpt: (jsObj, string) => Js.Nullable.t(jsObj) = "";
[@mel.get_index] external _arr: (jsObj, string) => array(jsObj) = "";

let getKind = (j: jsObj): string => _str(j, "kind");

let getMeta = (j: jsObj): meta => {
  let m = _obj(j, "meta");
  {parens: _bool(m, "parens"), start: _int(m, "start"), end_: _int(m, "end"), ghost: false};
};

let getBindingMeta = (j: jsObj): meta => {
  let m = _obj(j, "bindingMeta");
  {parens: _bool(m, "parens"), start: _int(m, "start"), end_: _int(m, "end"), ghost: false};
};

let getDeclMeta = (j: jsObj): meta => {
  let m = _obj(j, "declMeta");
  {parens: _bool(m, "parens"), start: _int(m, "start"), end_: _int(m, "end"), ghost: false};
};

let getParamMeta = (j: jsObj): meta => {
  let m = _obj(j, "paramMeta");
  {parens: _bool(m, "parens"), start: _int(m, "start"), end_: _int(m, "end"), ghost: false};
};

let getNameMeta = (j: jsObj): meta => {
  let m = _obj(j, "nameMeta");
  {parens: _bool(m, "parens"), start: _int(m, "start"), end_: _int(m, "end"), ghost: false};
};

let decodeHoleKind = (s: string): holeKind =>
  switch (s) {
  | "User" => User
  | "Synthesized" => Synthesized
  | "Auto" => Auto
  | _ => Synthesized
  };

let decodeBinOp = (s: string): binOp =>
  switch (s) {
  | "Eq" => Eq
  | "Neq" => Neq
  | "And" => And
  | "Or" => Or
  | _ => Eq
  };

/* === OL === */

let rec decodeOL = (j: jsObj): ol => {
  let meta = getMeta(j);
  let v = _obj(j, "value");
  let kind = getKind(v);
  let value =
    switch (kind) {
    | "OLIdentifier" => OLIdentifier(_str(v, "name"))
    | "OLHole" => OLHole(decodeHoleKind(_str(v, "hk")))
    | "OLAp" =>
      let f = decodeOL(_obj(v, "f"));
      let args = Array.map(decodeOL, _arr(v, "args")) |> Array.to_list;
      OLAp(f, args);
    | _ => OLHole(Synthesized)
    };
  {value, meta};
};

let decodeParam = (j: jsObj): param => {
  paramName: _str(j, "paramName"),
  paramType: decodeOL(_obj(j, "paramType")),
  paramMeta: getParamMeta(j),
  nameMeta: getNameMeta(j),
};

let decodeDecl = (j: jsObj): decl => {
  declName: _str(j, "declName"),
  params: Array.map(decodeParam, _arr(j, "params")) |> Array.to_list,
  retType: decodeOL(_obj(j, "retType")),
  declMeta: getDeclMeta(j),
  nameMeta: getNameMeta(j),
};

/* === ML types ===
   `mlToType` converts an ml expression (the raw annotation parsed as a
   regular expression) into the structured `mlType` if recognized. */

let rec mlToType = (t: ml): option(mlType) =>
  switch (t.value) {
  | Identifier("Term") => Some(MTerm)
  | Identifier("Sort") => Some(MSort)
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Tag") => Some(MTag)
  | Identifier("Signature") =>
    Some(MTuple([MTerm, MList(MTuple([MTerm, MTerm])), MTerm, MList(MTag)]))
  | Ap({value: Identifier("List"), _}, [arg]) =>
    switch (mlToType(arg)) {
    | Some(t) => Some(MList(t))
    | None => None
    }
  | Ap({value: Identifier("Result"), _}, [arg]) =>
    switch (mlToType(arg)) {
    | Some(t) => Some(MResult(t))
    | None => None
    }
  | Ap({value: Identifier("->"), _}, [l, r]) =>
    switch (mlToType(l), mlToType(r)) {
    | (Some(lt), Some(rt)) => Some(MArrow(lt, rt))
    | _ => None
    }
  | Tuple(items) =>
    let types = List.map(mlToType, items);
    if (List.for_all(t => t != None, types)) {
      Some(
        MTuple(
          List.map(
            t =>
              switch (t) {
              | Some(v) => v
              | None => MTerm
              },
            types,
          ),
        ),
      );
    } else {
      None;
    };
  | _ => None
  };

/* === Patterns === */

let rec decodePat = (j: jsObj): pat => {
  let meta = getMeta(j);
  let v = _obj(j, "value");
  let kind = getKind(v);
  let value =
    switch (kind) {
    | "PWildcard" => PWildcard
    | "PVar" => PVar(_str(v, "name"))
    | "PHole" => PHole
    | "PString" => PString(_str(v, "value"))
    | "PList" =>
      PList(Array.map(decodePat, _arr(v, "items")) |> Array.to_list)
    | "PCons" =>
      PCons(decodePat(_obj(v, "head")), decodePat(_obj(v, "tail")))
    | "PTuple" =>
      PTuple(Array.map(decodePat, _arr(v, "items")) |> Array.to_list)
    | "PAp" =>
      let head = decodePat(_obj(v, "head"));
      let args = Array.map(decodePat, _arr(v, "args")) |> Array.to_list;
      PAp(head, args);
    | _ => PWildcard
    };
  {value, meta};
};

/* === ML expressions === */

let rec decodeML = (j: jsObj): ml => {
  let meta = getMeta(j);
  let v = _obj(j, "value");
  let kind = getKind(v);
  let value =
    switch (kind) {
    | "Hole" => Hole(decodeHoleKind(_str(v, "hk")))
    | "Identifier" => Identifier(_str(v, "name"))
    | "StringLit" => StringLit(_str(v, "value"))
    | "TagLit" => TagLit(_str(v, "name"))
    | "Tuple" =>
      Tuple(Array.map(decodeML, _arr(v, "items")) |> Array.to_list)
    | "Asc" => Asc(decodeML(_obj(v, "expr")), decodeML(_obj(v, "type")))
    | "BinOp" =>
      BinOp(
        decodeBinOp(_str(v, "op")),
        decodeML(_obj(v, "left")),
        decodeML(_obj(v, "right")),
      )
    | "Ap" =>
      Ap(
        decodeML(_obj(v, "f")),
        Array.map(decodeML, _arr(v, "args")) |> Array.to_list,
      )
    | "List" =>
      List(Array.map(decodeML, _arr(v, "items")) |> Array.to_list)
    | "Cons" => Cons(decodeML(_obj(v, "head")), decodeML(_obj(v, "tail")))
    | "Fun" =>
      let params = Array.map(decodePat, _arr(v, "params")) |> Array.to_list;
      Fun(params, decodeML(_obj(v, "body")));
    | "Match" =>
      let arms =
        Array.map(
          arm => (decodePat(_obj(arm, "pat")), decodeML(_obj(arm, "body"))),
          _arr(v, "arms"),
        )
        |> Array.to_list;
      Match(decodeML(_obj(v, "scrut")), arms);
    | "If" =>
      If(
        decodeML(_obj(v, "cond")),
        decodeML(_obj(v, "then_")),
        decodeML(_obj(v, "else_")),
      )
    | "Let" =>
      Let(decodeBinding(_obj(v, "binding")), decodeML(_obj(v, "body")))
    | "BuilderError" => BuilderError
    | _ => Hole(Synthesized)
    };
  {value, meta};
}

and decodeBinding = (j: jsObj): binding => {
  let rawAnnotation =
    switch (Js.Nullable.toOption(_objOpt(j, "rawAnnotation"))) {
    | Some(o) => Some(decodeML(o))
    | None => None
    };
  let annotation =
    switch (rawAnnotation) {
    | Some(ml) => mlToType(ml)
    | None => None
    };
  {
    name: _str(j, "name"),
    annotation,
    rawAnnotation,
    rhs: decodeML(_obj(j, "rhs")),
    bindingMeta: getBindingMeta(j),
  };
};

let decodeMetaDef = (j: jsObj): metaDef => {
  let kind = getKind(j);
  switch (kind) {
  | "NewtagDef" =>
    let m = _obj(j, "defMeta");
    let meta = {
      parens: _bool(m, "parens"),
      start: _int(m, "start"),
      end_: _int(m, "end"),
      ghost: false,
    };
    NewtagDef(_str(j, "tag"), meta);
  | _ =>
    let binding = decodeBinding(_obj(j, "binding"));
    switch (kind) {
    | "SchemaDef" => SchemaDef(binding)
    | "CoerceDef" => CoerceDef(binding)
    | _ => LetDef(binding)
    };
  };
};

let decodeTagLine = (j: jsObj): tagLine => {
  let m = _obj(j, "lineMeta");
  let meta = {
    parens: _bool(m, "parens"),
    start: _int(m, "start"),
    end_: _int(m, "end"),
    ghost: false,
  };
  {tag: _str(j, "tag"), target: _str(j, "target"), lineMeta: meta};
};

/* === Blocks === */

let decodeBlock = (j: jsObj): block => {
  let kind = getKind(j);
  let readMeta = (key: string): meta => {
    let m = _obj(j, key);
    {
      parens: _bool(m, "parens"),
      start: _int(m, "start"),
      end_: _int(m, "end"),
      ghost: false,
    };
  };
  let readTagLines = (): list(tagLine) =>
    switch (Js.Undefined.toOption(Obj.magic(Js.Dict.get(Obj.magic(j), "tagLines")))) {
    | Some(arr) => Array.map(decodeTagLine, arr) |> Array.to_list
    | None => []
    };
  switch (kind) {
  | "Postulate" =>
    Postulate(
      readMeta("blockMeta"),
      Array.map(decodeDecl, _arr(j, "decls")) |> Array.to_list,
      readTagLines(),
    )
  | "Construct" =>
    Construct(
      _str(j, "schema"),
      readMeta("schemaMeta"),
      readMeta("blockMeta"),
      Array.map(decodeDecl, _arr(j, "decls")) |> Array.to_list,
      readTagLines(),
    )
  | "Meta" =>
    Meta(Array.map(decodeMetaDef, _arr(j, "defs")) |> Array.to_list)
  | _ => Postulate(defaultMeta, [], [])
  };
};

let decodeProgram = (j: array(jsObj)): program =>
  Array.map(decodeBlock, j) |> Array.to_list;
