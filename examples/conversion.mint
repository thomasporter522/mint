postulate
sort : sort
level : sort
lz : level
ls (l : level) : level
Ul (l : level) : Ul (ls l)
eq (l : level) (A : Ul l) (B : Ul l) (a : A) (b : B) : Ul l
refl (l : level) (A : Ul l) (a : A) : eq l A A a a
cast (l : level) (A : Ul l) (B : Ul l) (e : eq (ls l) (Ul l) (Ul l) A B) (a : A) : B
meta
schema definition =
  fun outer => fun s => match s with
  | [(f, [], ret, _),
     (f_eq, [], eq l ret ret f body, _)]
      => (Ok [body, (refl l ret body)])
  | _ => (Error "invalid definition")
  end
-- conversion [?] = 
--   fun (t_found, t_expected)
construct by definition
U1 : Ul (ls (ls lz))
U1-eq : eq (ls (ls (ls lz))) (Ul (ls (ls lz))) (Ul (ls (ls lz))) U1 (Ul (ls lz))
construct by definition
U : U1
U-eq : eq (ls (ls lz)) U1 U1 U (Ul lz)
