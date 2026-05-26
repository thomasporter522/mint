-- universe-levels.mint — ported from main.
-- A Russell-style universe hierarchy: U is parameterised by a level
-- and `U (l : level) : U (level-suc l)` self-references. The kernel
-- pre-binds the decl name before elaborating its own arg/ret types,
-- so `U (level-suc l)` resolves to the same `U` being declared.

-- Bootstrap U (the impredicative top) in its own postulate block so
-- the second `type term += U of term` lands in a separate OCaml
-- phrase — extension constructors must be unique per phrase.
postulate
U : U
level : U
level-zero : level
level-suc (l : level) : level
end

postulate
U (l : level) : U (level-suc l)
N : U level-zero
zero : N
point (l : level) (A : U l) (a : A) : U (level-suc l)
point-zero : point level-zero N zero
end
