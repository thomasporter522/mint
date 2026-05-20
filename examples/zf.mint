-- requires formalizing FOL...

postulate 
sort : sort
prop : sort
-- and (p1 p2 : prop) : prop
-- implies (p1 p2 : prop) : prop
ctx : sort
open-prop (c : ctx) : sort
ctx-nil : ctx 
ctx-cons (c : ctx) (x : open-prop c) : ctx 
-- hypo-prof (c : ctx) (p : prop)


set : sort 
el (s1 s2 : set) : prop 
eq (s1 s2 : set) : prop
ext (s1 s2 : set) (p : ?) : eq s1 s2
