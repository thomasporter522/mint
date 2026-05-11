-- postulate 
-- sort : sort
-- prop : sort 
-- proof (a : prop) : sort 
-- and (a1 a2 : prop) : prop 
-- pair (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2) : proof (and a1 a2)

-- mythm-stmt (a1 a2 a3 : prop) (p1 : proof a1) (p2 : proof a2) (p3 : proof a3) (body 
--     : proof (and (and a1 a2) a3)) : sort
-- mythm-pf (a1 a2 a3 : prop) (p1 : proof a1) (p2 : proof a2) (p3 : proof a3) 
--     : mythm-stmt a1 a2 a3 p1 p2 p3 (pair ? ?)

-- end

-- postulate 
-- sort : sort
-- prop : sort 
-- proof (a : prop) : sort 
-- and (a1 a2 : prop) : prop 
-- pair (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2) : proof (and a1 a2)

-- mythm-stmt (a1 a2 a3 : prop) (p1 : proof a1) (p2 : proof a2) (p3 : proof a3) (body 
--     : proof (and (and a1 a2) a3)) : sort
-- mythm-pf (a1 a2 a3 : prop) (p1 : proof a1) (p2 : proof a2) (p3 : proof a3) 
--     : mythm-stmt a1 a2 a3 p1 p2 p3 (pair (pair p1 p2) ?)

-- end

postulate 
sort : sort
prop : sort 
proof (a : prop) : sort 
and (a1 a2 : prop) : prop 
pair (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2) : proof (and a1 a2)

mythm-stmt (a1 a2 a3 : prop) (body : proof (and (and a1 a2) a3)) : sort
mythm-pf (a1 a2 a3 : prop) (p1 : proof a1) (p2 : proof a2) (p3 : proof a3) 
    : mythm-stmt (pair (pair p1 p2) p3)

end