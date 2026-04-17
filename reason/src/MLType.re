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

/* Pretty-print a type.
   Examples:
     MTerm => "Term"
     MList(MTerm) => "List Term"
     MArrow(MTerm, MTerm) => "Term -> Term"
     MPair(MTerm, MList(MTerm)) => "(Term, List Term)"
     MArrow(MList(MTerm), MResult(MTerm)) => "List Term -> Result Term" */
let rec printType =
  fun
  | MTerm => failwith("TODO")
  | MSort => failwith("TODO")
  | MBool => failwith("TODO")
  | MString => failwith("TODO")
  | MList(t) => failwith("TODO")
  | MResult(t) => failwith("TODO")
  | MPair(a, b) => failwith("TODO")
  | MArrow(a, b) => failwith("TODO")

/* Like printType, but wraps compound types in parentheses.
   Compound = MList, MResult, MArrow. Simple = everything else.
   Used when a type appears as an argument to a type constructor.
   Examples:
     MTerm => "Term"  (no parens, simple)
     MList(MTerm) => "(List Term)"  (parens, compound)
     MArrow(MTerm, MTerm) => "(Term -> Term)"  (parens, compound)
     MPair(MTerm, MTerm) => "(Term, Term)"  (no parens, simple) */
and printTypeAtom =
  fun
  | (MTerm | MSort | MBool | MString | MPair(_, _)) as t => printType(t)
  | t => "(" ++ printType(t) ++ ")";

/* Structural equality on types. */
let rec eqType = (a: mlType, b: mlType): bool =>
  failwith("TODO");
