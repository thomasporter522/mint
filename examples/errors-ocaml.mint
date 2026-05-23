// example-ocaml-err.mint — OL elaboration passes, but the meta block
// contains a deliberate OCaml type error. We want Toploop's diagnostic
// to point at the Mint source line (via the emitted #line directive),
// not at our synthesized phrase coordinates.

postulate
Sort : Sort
Nat : Sort
Zero : Nat
end

meta
let oops : int = "this is a string, not an int"
;;
end
