-- holes-main.mint — ported from main. Tests holes (`?`) in OL terms and
-- the "Unbound identifier" diagnostic for undeclared names.

postulate
Sort : Sort
U : Sort
eq (A : U) (B : U) (a : A) (b : B) : U
D : U
x : D
y : eq D D x ?
z : eq D D x badvar
end
