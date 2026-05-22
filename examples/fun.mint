postulate
sort : sort
U : U
eq (A B : U) (a : A) (b : B) : U
refl (A : U) (a : A) : eq a a
cast (A B : U) (e : eq A B) (a : A) : B
sym (A B : U) (a : A) (b : B) (e1 : eq a b) : eq b a
trans (A B C : U) (a : A) (b : B) (c : C) (e1 : eq a b) (e2 : eq b c) : eq a c
meta 
    newtag #reduction
postulate 
sto (A B : U) : U 
sap (A B : U) (f : sto A B) (a : A) : B
to (A : U) : sto (sto A U) U
ap (A : U) (B : sto A U) (f : sap (to A) B) (a : A) : sap B a
postulate 
cast-eq (A B : U) (e : eq A B) (a : A) : eq (cast e a) a
#reduction cast-eq
sto-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (sto A1 B1) (sto A2 B2)
sap-cong (A1 A2 B1 B2 : U) (f1 : sto A1 B1) (f2 : sto A2 B2) (a1 : A1) (a2 : A2) (e1 : eq f1 f2) (e2 : eq a1 a2) : eq (sap f1 a1) (sap f2 a2)
-- eq-cong (A1 A2 B1 B2 : U) (e1 : eq A1 A2) (e2 : eq B1 B2) : eq (eq A1 B1) (eq A2 B2)
meta 
  --     consistent : (Term -> (Term -> Bool)) = fun a => fun b =>
  --       let pa = (decompose a) in
  --       let pb = (decompose b) in
  --       let ha = (fst pa) in
  --       let hb = (fst pb) in
  --       if (ha == ?) then true else
  --       if (hb == ?) then true else
  --       if (ha == hb) then (consistent-list (snd pa) (snd pb))
  --       else false end end end
  --     consistent-list : ((List Term) -> ((List Term) -> Bool)) = fun xs => fun ys =>
  --       match (xs, ys) with
  --       | ([], []) => true
  --       | ([], _::_) => false
  --       | (_::_, []) => false
  --       | (x :: xt, y :: yt) =>
  --           if (consistent x y) then (consistent-list xt yt) else false end
  --       end
  --     -- beta-reduce : ((List Signature) -> (Term -> (Term, Term))) = fun ctx => fun term =>
  --     --   let sub = match term with
  --     --     | (ap A B f a) =>
  --     --       let fr = (beta-reduce ctx f) in
  --     --       let ar = (beta-reduce ctx a) in
  --     --       ((ap A B (fst fr) (fst ar)), (ap (ap cong-ap (snd fr)) (snd ar)))
  --     --     | (to A B) =>
  --     --       let ar = (beta-reduce ctx A) in
  --     --       let br = (beta-reduce ctx B) in
  --     --       ((to (fst ar) (fst br)), (cong-to (snd ar) (snd br)))
  --     --     | _ => (term, (refl ? term))
  --     --     end in
  --     --   let st = (fst sub) in
  --     --   let sp = (snd sub) in
  --       -- match (try-top ctx term) with
  --       -- | Ok (next-term, next-proof) =>
  --       --   let (final-term, final-proof) = (beta-reduce ctx next-term) in
  --       --   let chain1 = (ap (ap trans sp) next-proof) in
  --       --   (final, (ap (ap trans chain1) final-proof))
  --       -- | Error _ => (st, sp)
  --       -- end
  --     beta-convert : (List (Term, List (Term, Term), Term, List Tag)) -> ? = 
  --       fun ctx => fun t1 => fun t2 => 
  --       let (t1r, eq1) = (head-reduce t1) in  
  --       let (t2r, eq2) = (head-reduce t2) in 
  --         (if (t1r == ?) then ? else ?)
  --     coerce beta = fun ctx => fun expected => fun found => fun contents =>
  --       match (beta-convert ctx expected found) with 
  --       | Ok proof => (Ok (cast proof contents))
  --       | Error _ => (Error "beta normal forms inconsistent")
  --       end
postulate 
lk (X A : U) : sto A (sto X A)
lk-eq (X A : U) (a : A) (x : X) : eq (sap (sap (lk X A) a) x) a
#reduction lk-eq 
lsto (X : U) (A B : sto X U) : sto X U
lsto-eq (X : U) (A B : sto X U) (x : X) : eq (sap (lsto A B) x) (sto (sap A x) (sap B x))
#reduction lsto-eq 
lsap (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) : sto X B
lsap-eq (X : U) (A : sto X U) (B : U) (f : sap (to X) (lsto A (sap lk B))) (a : sap (to X) A) (x : X) : 
    eq (sap (lsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
#reduction lsap-eq
-- clsap (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) : sap (to X) B
-- clsap-eq (X : U) (A B : sto X U) (f : sap (to X) (lsto A B)) (a : sap (to X) A) (x : X) : 
--     eq (ap (clsap A B f a) x) (sap (cast lsto-eq (ap f x)) (ap a x))
-- #reduction clsap-eq
lto (X : U) (A : sto X U) : sap (to X) (lsto (lsto A (sap lk U)) (sap lk U))
lto-eq (X : U) (A : sto X U) (x : X) : eq (ap (lto X A) x) (to (sap A x))
#reduction lto-eq

lap (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) : sap (to X) (lsap B a)
lap-eq (X : U) (A : sto X U) (B : sap (to X) (lsto A (sap lk U)))
    (f : sap (to X) (lsap (lto A) B)) (a : sap (to X) A) (x : X) : 
    eq (ap (lap f a) x) 
        (ap (cast (trans (lsap-eq) (sap-cong (trans cast-eq lto-eq) (sym (cast-eq (trans lsto-eq (sto-cong refl lk-eq)) (ap B x))))) 
                (ap f x))
                (ap a x))
#reduction lap-eq
