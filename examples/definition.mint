postulate
U : U
(eq (A : U) (B : U) (a : A) (b : B)) : U
(refl (A : U) (a : A)) : (eq A A a a)
(trans (A : U) (a : A) (b : A) (c : A) (e1 : (eq A A a b)) (e2 : (eq A A b c))) : (eq A A a c)
D : U 
K : D
S : D 
(ap (f : D) (a : D)) : D
(ap-K (x : D) (y : D)) : (eq D D (ap (ap K x) y) x)
(ap-S (x : D) (y : D) (z : D)) : (eq D D (ap (ap (ap S x) y) z) (ap (ap x z) (ap y z)))
(ap-cong (f : D) (g : D) (x : D) (e : (eq D D f g))) : (eq D D (ap f x) (ap g x))
meta
schema definition =
  fun s => match s with
  | [(f, [], ret),
     (f_eq, [], eq ret ret f body)]
      => (Ok [body, (refl ret body)])
  | _ => (Error "invalid definition")
  end
construct by definition
I : D
I-eq : (eq D D I (ap (ap S K) K))
meta
schema arg-definition =
  fun s => match s with
  | [(f, params, ret),
     (f_eq, params, eq ret ret applied body)]
      => if applied == (foldl (fun acc => fun p => match p with | (x, t) => (acc x) end) f params)
         then (Ok [body, (refl ret body)])
         else (Error "LHS mismatch")
         end
  | _ => (Error "invalid arg-definition")
  end
construct by arg-definition
(ap-I (x : D)) : (eq D D (ap I x) x)
(ap-I-pf (x : D)) : (eq (eq D D (ap I x) x) (eq D D (ap I x) x) (ap-I x) (
  trans D 
  (ap I x) (ap (ap (ap S K) K) x) x 
  (ap-cong I (ap (ap S K) K) x I-eq) 
  (trans D (ap (ap (ap S K) K) x) (ap (ap K x) (ap K x)) x 
  (ap-S K K x) 
  (ap-K x (ap K x)))))
end