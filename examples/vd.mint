postulate 
// sort : sort 
U : U

-- -> : (A : U) -> (B : A -> U) -> U
to (A : U) : ap ? ? (to (ap ? ? (to A) (k A U U))) U
-- k : (X : U) -> (A : U) -> A -> X -> A
k (X A : U) (a : A) : (ap ? ? (to X) (k X U A))
-- ap : (A : U) -> (B : A -> U) -> (f : A -> B) -> (a : A) -> B a
ap (A : U) (B : ap ? ? (to A) (k A U U)) (f : ap ? ? (to A) B) (a : A) : ap A (k A U U) B a