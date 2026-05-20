postulate
sort : sort
-- universe levels
level : sort
lz : level
ls (l : level) : level
lmax (l1 l2 : level) : level
Ul (l : level) : Ul (ls l)
level-eq (l1 l2 : level) : sort
lmax-refl (l : level) : level-eq l l
lmax-sym (l1 l2 : level) (eq : level-eq l1 l2) : level-eq l2 l1
lmax-idem (l : level) : level-eq (lmax l l) l
-- equations
eq (l1 l2 : level) (A : Ul l1) (B : Ul l2) (a : A) (b : B) : Ul (lmax l1 l2)
-- functions
to (l1 l2 : level) (A : Ul l1) (B : Ul l2) : Ul (lmax l1 l2)
-- fn (l1 l2 : level) (A : Ul l1) [x : A] (B : Ul l2) (body[x] : B) : to A B
ap (l1 l2 : level) (A : Ul l1) (B : Ul l2) (f : to A B) (a : A) : B
-- beta (l1 l2 : level) (A : Ul l1) [x : A] (B : Ul l2) (body[x] : B) (a : A) : eq (ap (fn x B body[x]) a) body[a]

-- dto (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) : Ul (lmax l1 l2)
-- could do this:
-- dfn (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) (body[x] : B[x]) : Ul (lmax l1 l2)
-- dap (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) (f : dto A x B[x]) (a : A) : B[a]
-- dbeta (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) (body[x] : B[x]) (a : A) : eq (dap (dfn x B[x] body[x]) a) body[a]
-- but I think this is better:
-- dfn (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) [y : A] (body[y] : B[y]) : Ul (lmax l1 l2)
-- dap (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) (f : dto A x B[x]) (a : A) : B[a]
-- dbeta (l1 l2 : level) (A : Ul l1) [x : A] (B[x] : Ul l2) [y : A] (body[y] : B[y]) (a : A) : eq (dap (dfn z body[z]) a) body[a]

-- let (l1 l2 : level) (A : Ul l1) (B : Ul l2) [x : A] (def : A) (body[x] : B) : B
-- zeta (l1 l2 : level) (A : Ul l1) (B : Ul l2) [x : A] (def : A) (body[x] : B) :
    -- eq (let l1 l2 A B x def body[x]) body[def]
