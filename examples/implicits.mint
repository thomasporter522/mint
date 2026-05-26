// implicits.mint — when a constructor is underapplied, the missing
// args are the FIRST n (leading ghost metas). Each ghost carries the
// expected type recorded at allocation, and `unify` does type-level
// propagation: when a meta gets solved to a term, its expected type
// is unified against the term's computed type, which can transitively
// solve other metas.
//
// Each leading ghost surfaces in the editor as a `…` anchored at the
// head's end, with the inferred subterm in the hover tooltip.
//
// `eq (T : U) (a : T) (b : T) : U` — applying it with just two args
// leaves `T` as the leading implicit. The elaborator solves `T = Nat`
// from the type of either argument (`Zero : Nat`).

postulate
Sort : Sort
U : Sort
Nat : U
Zero : Nat
eq (T : U) (a : T) (b : T) : U
example : eq Zero
end
