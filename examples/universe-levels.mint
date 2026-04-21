postulate
sort : sort 
level : sort
level-zero : level
(level-suc (l : level)) : level
(U (l : level)) : (U (level-suc l))
N : (U level-zero)
zero : N
(point (l : level) (A : (U l)) (a : A)) : (U (level-suc l))
point-zero : (point level-zero N zero)
end