// example-err.mint — exercises the OL checker's diagnostic path.
//
// Three intentional errors:
//   1. `Bogus` is referenced as a type but never declared.
//   2. `Zero (n : Nat) : Nat` is called with one arg but declared nullary.
//   3. `Foo : Mystery` references an undeclared `Mystery`.

postulate
Nat : Sort
Zero : Nat
Suc (n : Bogus) : Nat
end

meta
let f x = Zero x ;;   // arity mismatch will land in OCaml-side error
end

construct by enum_schema
Foo : Mystery
end
