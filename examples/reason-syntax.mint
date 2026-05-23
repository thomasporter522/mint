// example-reason.mint — meta block written in Reason syntax. Mint
// shells out to refmt to convert Reason → OCaml before sending it to
// Toploop.

postulate
Sort : Sort
Nat : Sort
Zero : Nat
Suc (n : Nat) : Nat
Tag : Sort
end

meta
let rec string_of_term = (t) =>
  switch (t) {
  | Sort => "Sort"
  | Tag => "Tag"
  | Nat => "Nat"
  | Zero => "Zero"
  | Suc(m) => "Suc(" ++ string_of_term(m) ++ ")"
  | _ => "<extension>"
  };

let enum_schema = (_outer: list(signature), sigs: list(signature))
    : result(list(term), string) => {
  let rec build = (n) =>
    if (n == 0) {
      Zero;
    } else {
      Suc(build(n - 1));
    };
  Ok(List.mapi((i, _) => build(i), sigs));
};
end

construct by enum_schema
Foo : Tag
Bar : Tag
Baz : Tag
end
