/* Decode the JS AST produced by web/src/frontend/builder.ts into the native
   OCaml AST defined in Term.re. Field names and `kind` discriminators
   match ast.ts exactly — keep them in sync. */

open Term;

/* === JS interop === */

type jsObj;

[@mel.send] external getString: (jsObj, string) => string = "get";

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

let readMetaField = (j: jsObj, key: string): meta => {
  let m = _obj(j, key);
  {
    parens: _bool(m, "parens"),
    start: _int(m, "start"),
    end_: _int(m, "end"),
    ghost: None,
  };
};

let getMeta = (j: jsObj): meta => readMetaField(j, "meta");

let decodeBinOp = (s: string): binOp =>
  switch (s) {
  | "Eq" => Eq
  | "Neq" => Neq
  | "And" => And
  | "Or" => Or
  | _ => Eq
  };

let decodeStringMeta = (j: jsObj): stringMeta => {
  string: _str(j, "string"),
  meta: getMeta(j),
};

/* === OL === */

let rec decodeOL = (j: jsObj): ol => {
  let meta = getMeta(j);
  let v = _obj(j, "value");
  let kind = getKind(v);
  let value =
    switch (kind) {
    | "OLHole" => OLHole
    | "OLAp" =>
      let f = decodeStringMeta(_obj(v, "f"));
      let args = Array.map(decodeOL, _arr(v, "args")) |> Array.to_list;
      OLAp(f, args);
    | _ => OLHole
    };
  {value, meta};
};

let decodeDeclArg = (j: jsObj): declArg => {
  declArgName: decodeStringMeta(_obj(j, "declArgName")),
  declArgType: decodeOL(_obj(j, "declArgType")),
  declArgMeta: readMetaField(j, "declArgMeta"),
};

let decodeDeclLine = (j: jsObj): declLine => {
  declName: decodeStringMeta(_obj(j, "declName")),
  args: Array.map(decodeDeclArg, _arr(j, "args")) |> Array.to_list,
  retType: decodeOL(_obj(j, "retType")),
  declMeta: readMetaField(j, "declMeta"),
};

let decodeTagLine = (j: jsObj): tagLine => {
  tag: _str(j, "tag"),
  target: _str(j, "target"),
  lineMeta: readMetaField(j, "lineMeta"),
};

let decodeOLLine = (j: jsObj): olLine => {
  let kind = getKind(j);
  switch (kind) {
  | "Tag" => Tag(decodeTagLine(j))
  | _ => Decl(decodeDeclLine(j))
  };
};

/* === ML types ===
   `mlToType` converts an ml expression (the raw annotation parsed as a
   regular expression) into the structured `mlType` if recognized. OL
   term types are represented as `MOLTerm(ol)`; when an annotation slot
   was previously the bare `MTerm`, we now stand in an OL hole. */

let rec mlToType = (t: ml): option(mlType) =>
  switch (t.value) {
  | Identifier("Bool") => Some(MBool)
  | Identifier("String") => Some(MString)
  | Identifier("Tag") => Some(MTag)
  | Identifier("Signature") =>
    let oh = mkOL(OLHole);
    Some(
      MTuple([
        MOLTerm(oh),
        MList(MTuple([MOLTerm(oh), MOLTerm(oh)])),
        MOLTerm(oh),
        MList(MTag),
      ]),
    );
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
              | None => MOLTerm(mkOL(OLHole))
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
    | "PString" => PString(_str(v, "value"))
    | "PList" =>
      PList(Array.map(decodePat, _arr(v, "items")) |> Array.to_list)
    | "PCons" =>
      PCons(decodePat(_obj(v, "head")), decodePat(_obj(v, "tail")))
    | "PTuple" =>
      PTuple(Array.map(decodePat, _arr(v, "items")) |> Array.to_list)
    | "POLAp" =>
      let head = _str(v, "head");
      let args = Array.map(decodePat, _arr(v, "args")) |> Array.to_list;
      POLAp(head, args);
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
    | "Hole" => Hole
    | "Meta" => Meta(_int(v, "id"))
    | "Identifier" => Identifier(_str(v, "name"))
    | "StringLit" => StringLit(_str(v, "value"))
    | "TagLit" => TagLit(_str(v, "name"))
    | "Tuple" =>
      Tuple(Array.map(decodeML, _arr(v, "items")) |> Array.to_list)
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
      Let(decodeLetBinding(_obj(v, "binding")), decodeML(_obj(v, "body")))
    | _ => Hole
    };
  {value, meta};
}

and decodeLetBinding = (j: jsObj): letBinding => {
  let annotation =
    switch (Js.Nullable.toOption(_objOpt(j, "rawAnnotation"))) {
    | Some(o) => mlToType(decodeML(o))
    | None => None
    };
  {
    pat: decodePat(_obj(j, "pat")),
    annotation,
    definition: decodeML(_obj(j, "definition")),
    bindingMeta: readMetaField(j, "bindingMeta"),
  };
};

let decodeBinding = (j: jsObj): binding => {
  let annotation =
    switch (Js.Nullable.toOption(_objOpt(j, "rawAnnotation"))) {
    | Some(o) => mlToType(decodeML(o))
    | None => None
    };
  {
    pat: _str(j, "pat"),
    annotation,
    definition: decodeML(_obj(j, "definition")),
    bindingMeta: readMetaField(j, "bindingMeta"),
  };
};

let decodeMetaDef = (j: jsObj): metaDef => {
  let kind = getKind(j);
  switch (kind) {
  | "NewtagDef" => NewtagDef(_str(j, "tag"), readMetaField(j, "defMeta"))
  | "SchemaDef" => SchemaDef(decodeBinding(_obj(j, "binding")))
  | "CoerceDef" => CoerceDef(decodeBinding(_obj(j, "binding")))
  | _ => LetDef(decodeLetBinding(_obj(j, "binding")))
  };
};

/* === Blocks === */

let decodeBlock = (j: jsObj): block => {
  let kind = getKind(j);
  switch (kind) {
  | "Postulate" =>
    Postulate({
      postulateMeta: readMetaField(j, "postulateMeta"),
      lines: Array.map(decodeOLLine, _arr(j, "lines")) |> Array.to_list,
    })
  | "Construct" =>
    Construct({
      schema: _str(j, "schema"),
      schemaMeta: readMetaField(j, "schemaMeta"),
      lines: Array.map(decodeOLLine, _arr(j, "lines")) |> Array.to_list,
    })
  | "Meta" =>
    Meta(Array.map(decodeMetaDef, _arr(j, "defs")) |> Array.to_list)
  | _ => Postulate({postulateMeta: defaultMeta, lines: []})
  };
};

let decodeProgram = (j: array(jsObj)): program =>
  Array.map(decodeBlock, j) |> Array.to_list;
