postulate
  -- TODO
meta
  schema enum = ? -- TODO
construct by enum
  falsity : U 
  (falsity-case (M : U) (scrutinee : falsity)) : M
construct by enum
  unit : U 
  trivial : unit
  (unit-case (M : U) (trivial-case : M) (scrutinee : unit)) : M
  (unit-case-trivial (M : U) (trivial-case : M)) : 
    (eq M M (unit-case M trivial-case trivial) trivial-case)
construct by enum
  bool : U 
  true : bool 
  false : bool
  (bool-case (M : U) (true-case : M) (false-case : M) (scrutinee : bool)) : M
  (bool-case-true (M : U) (true-case : M) (false-case : M)) : 
    (eq M M (bool-case M true-case false-case true) true-case)
  (bool-case-false (M : U) (true-case : M) (false-case : M)) : 
    (eq M M (bool-case M true-case false-case false) false-case)
end