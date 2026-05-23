// example-multiline.mint — exercises indent-based decl continuation.
//
// A physical line that's indented STRICTLY MORE than the first line of
// the current decl is treated as a continuation. A line at the same
// indent (or less) starts a new decl. `end` finalizes any pending decl
// and closes the block.

postulate
Sort : Sort
U : Sort

eq (A : U) (B : U)
   : U

refl
  (A : U)
  : eq A U

simple : U

continued
  : U
end
