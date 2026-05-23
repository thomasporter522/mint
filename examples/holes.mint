// example-holes.mint — holes (`?`) in OL terms. The elaborator
// allocates a meta for each one and reports the inferred goal type.

postulate
Sort : Sort
Nat : Sort
Zero : Nat
Suc (n : Nat) : Nat
Pair (a : Nat) (b : Sort) : Nat
end

// A decl whose retType has two holes — the kernel reports each one's
// expected type from elaborating the surrounding `Pair`.
postulate
Twins : Pair ? ?
end
