postulate
sort : sort
prop : sort
proof (a : prop) : sort 
and (a1 a2 : prop) : prop 
pair (a1 a2 : prop) (p1 : proof a1) (p2 : proof a2) : proof (and a1 a2)
first (a1 a2 : prop) (p1 : proof (and a1 a2)) : proof a1
second (a1 a2 : prop) (p1 : proof (and a1 a2)) : proof a2

mythm-stmt (a1 a2 a3 : prop) (body : proof (and (and a1 a2) a3)) : sort

mythm-pf 
    (a1 a2 a3 : prop) 
    (p1 : proof a1) 
    (p2 : proof a2) 
    (p3 : proof a3)
    (arg : mythm-stmt a1 a2 a3 ⟐) : sort

meta
    schema magic =
        fun ctx => fun s =>
        match s with
        | [(_, args, t, _)] =>
            let empty-params : (List (Term, Term)) = [] in
            let empty-tags : (List Tag) = [] in
            let arg-sigs : (List Signature) =
              (foldl
                (fun acc => fun p => ((fst p), empty-params, (snd p), empty-tags) :: acc)
                [] args) in
            match (canonical (append arg-sigs ctx) t) with
            | Ok w => (Ok [w])
            | Error msg => (Error "Magic machine broke")
            end
        | _ => (Error "Single line only")
        end
construct by magic
mythm (a1 a2 a3 : prop) 
    (p1 : proof a1) 
    (p2 : proof a2) 
    (p3 : proof a3) : proof (and (and a1 a2) a3)