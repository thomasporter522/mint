/* ML type system for the meta-language.
   Simply-typed with Term, Sort, String, List, Result, pairs, and functions. */

type mlType =
  | MTerm
  | MSort
  | MBool
  | MString
  | MList(mlType)
  | MResult(mlType)
  | MPair(mlType, mlType)
  | MArrow(mlType, mlType);

let rec printType =
  fun
  | MTerm => "Term"
  | MSort => "Sort"
  | MBool => "Bool"
  | MString => "String"
  | MList(t) => "List " ++ printTypeAtom(t)
  | MResult(t) => "Result " ++ printTypeAtom(t)
  | MPair(a, b) => "(" ++ printType(a) ++ ", " ++ printType(b) ++ ")"
  | MArrow(a, b) => printTypeAtom(a) ++ " -> " ++ printType(b)
and printTypeAtom =
  fun
  | (MTerm | MSort | MString | MPair(_, _)) as t => printType(t)
  | t => "(" ++ printType(t) ++ ")";

let rec eqType = (a: mlType, b: mlType): bool =>
  switch (a, b) {
  | (MTerm, MTerm)
  | (MSort, MSort)
  | (MBool, MBool)
  | (MString, MString) => true
  | (MList(a), MList(b)) => eqType(a, b)
  | (MResult(a), MResult(b)) => eqType(a, b)
  | (MPair(a1, a2), MPair(b1, b2)) => eqType(a1, b1) && eqType(a2, b2)
  | (MArrow(a1, a2), MArrow(b1, b2)) => eqType(a1, b1) && eqType(a2, b2)
  | _ => false
  };
