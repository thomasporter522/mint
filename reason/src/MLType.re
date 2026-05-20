/* ML type system — re-exported from Term.re where the canonical definition lives. */

type mlType = Term.mlType =
  | MTerm
  | MBool
  | MString
  | MTag
  | MList(mlType)
  | MResult(mlType)
  | MTuple(list(mlType))
  | MArrow(mlType, mlType);

let rec printType =
  fun
  | MTerm => "Term"
  | MBool => "Bool"
  | MString => "String"
  | MTag => "Tag"
  | MList(t) => "List " ++ printTypeAtom(t)
  | MResult(t) => "Result " ++ printTypeAtom(t)
  | MTuple(items) => "(" ++ String.concat(", ", List.map(printType, items)) ++ ")"
  | MArrow(a, b) => printTypeAtom(a) ++ " -> " ++ printTypeAtom(b)
and printTypeAtom =
  fun
  | (MTerm | MBool | MString | MTag | MTuple(_)) as t => printType(t)
  | t => "(" ++ printType(t) ++ ")";

let rec eqType = (a: mlType, b: mlType): bool =>
  switch (a, b) {
  | (MTerm, MTerm)
  | (MBool, MBool)
  | (MString, MString)
  | (MTag, MTag) => true
  | (MList(a), MList(b)) => eqType(a, b)
  | (MResult(a), MResult(b)) => eqType(a, b)
  | (MTuple(as_), MTuple(bs)) =>
    List.length(as_) == List.length(bs)
    && List.for_all2(eqType, as_, bs)
  | (MArrow(a1, a2), MArrow(b1, b2)) => eqType(a1, b1) && eqType(a2, b2)
  | _ => false
  };
