open Utils;
open Grammar;
open Term;
open Parser;

let combineTerms =
  fun
  | [] => mk(Hole(true))
  | [t] => t
  | [first, ..._] as ts => {
      let last = List.nth(ts, List.length(ts) - 1);
      let t = mk(Ap(first, List.tl(ts)));
      {...t, meta: {...t.meta, start: first.meta.start, end_: last.meta.end_}};
    };

let localize = (t: term, token: ranged(primaryToken)): term =>
  {...t, meta: {...t.meta, start: token.start, end_: token.end_}};

let isToken = (name: string, tok: primaryToken): bool =>
  switch (tok) {
  | TNamed(n) => n == name
  | _ => false
  };

let isCommaToken = (tok: primaryToken): bool =>
  switch (tok) {
  | TNamed("," | ",p" | ",l") => true
  | _ => false
  };

/* TODO: buildTerms
   Build a single term from a list of sharded open forms.
   Concatenate the results of buildSharded for each item,
   then combine with combineTerms. */
let rec buildTerms = (_fs: list(sharded(openForm))): term =>
  failwith("TODO: buildTerms")

/* TODO: buildChild
   Build a term from an optional right child and its preceding unforms.
   If the child is Some(f), combine buildUnforms(unforms) @ [buildForm(f)].
   If None, just combine buildUnforms(unforms). */
and buildChild = (_unforms, _form) =>
  failwith("TODO: buildChild")

/* TODO: buildItems
   Build a list of terms from sharded forms, keeping only Form entries.
   Filter out Unform entries — they are whitespace/shards between declarations
   inside blocks. Each Form(f) becomes buildForm(f). */
and buildItems = (_items: list(sharded(openForm))): list(term) =>
  failwith("TODO: buildItems")

/* TODO: faceToken
   Extract the token name from a closedForm.
   - CMatch(_, _, {value: TNamed(n), _}) => n
   - CHead({value: TNamed(n), _}) => n
   - otherwise => "" */
and faceToken = (_form: closedForm): string =>
  failwith("TODO: faceToken")

/* TODO: buildBlock
   Given a keyword string, block contents, and an optional rest term,
   build the appropriate block AST node.
   - "postulate" => Postulate(body, rest)
   - "meta" => Meta(body, rest)
   - "construct" => Construct(by, decls, rest)
     Special case: if body is empty and rest is Some, return rest directly
     (this handles "construct by ..." where content is in the "by" block)
   - "by" => Construct(name, decls, rest)
     The first item in body is the schema name, the rest are declarations */
and buildBlock = (_keyword, _contents, _rest): term =>
  failwith("TODO: buildBlock")

/* TODO: buildBlocks
   Dispatch to buildBlock for chained blocks.
   - CHead(_) => call buildBlock with the keyword
   - CMatch(inner, innerItems, _) => recurse on inner, passing the current
     block as the rest parameter. This chains postulate...meta...construct. */
and buildBlocks = (_form, _contents, _rest): term =>
  failwith("TODO: buildBlocks")

/* TODO: buildLeftChild
   Build the left child of an infix operator.
   If left is Some(f), combine [buildForm(f), ...buildUnforms(leftUf)].
   If None, just combine buildUnforms(leftUf). */
and buildLeftChild = (_left, _leftUf) =>
  failwith("TODO: buildLeftChild")

/* TODO: buildInfix
   Build an infix operator node.
   Takes a constructor function (e.g., (l, r) => Asc(l, r)), the left child,
   left unforms, the operator token (for localization), right unforms, and
   right child. Combines left via buildLeftChild, right via buildChild,
   applies the constructor, and localizes to the operator token's position. */
and buildInfix = (_constructor, _left, _leftUf, _tok, _rightUf, _right) =>
  failwith("TODO: buildInfix")

/* TODO: isMatchChain
   Detect whether a closedForm is a match...with...end chain.
   Recurse through CMatch layers — the outermost tokens should be
   "end", "=>", "|", or "with". The innermost CHead must be "match". */
and isMatchChain = (_cf: closedForm): bool =>
  failwith("TODO: isMatchChain")

/* TODO: collectMatchBranches
   Walk inward through the CMatch nesting to collect (pattern, body) pairs.
   - Base: CMatch(CHead("match"), scrutItems, "with") => (scrutinee, [])
   - Step: CMatch(CMatch(deeper, patItems, "=>"), bodyItems, "|" or "end")
     => collect one branch (pat, body) and recurse on deeper
   Returns (scrutinee, branches) in source order. */
and collectMatchBranches = (_cf: closedForm): (term, list((term, term))) =>
  failwith("TODO: collectMatchBranches")

/* TODO: isIfChain
   Detect whether a closedForm is an if...then...else...end chain.
   Recurse through CMatch layers — tokens should be "end", "else", or "then".
   The innermost CHead must be "if". */
and isIfChain = (_cf: closedForm): bool =>
  failwith("TODO: isIfChain")

/* TODO: buildIfChain
   Destructure the four-deep CMatch nesting:
     CMatch(CMatch(CMatch(CHead("if"), condItems, "then"), thenItems, "else"), elseItems, "end")
   Build If(cond, thenBranch, elseBranch). Return BuilderError if the shape
   doesn't match. */
and buildIfChain = (_cf: closedForm): term =>
  failwith("TODO: buildIfChain")

/* TODO: collectBracketElements
   Walk the CMatch nesting from outside in, collecting element groups.
   - CHead(open_) => (open_, [])  -- base case, return the opening bracket name
   - CMatch(inner, items, tok) when tok is a comma or closing bracket
     => recurse on inner, append items to the list
   Returns (openBracket, list of element groups) in source order. */
and collectBracketElements = (_cf: closedForm): (string, list(list(sharded(openForm)))) =>
  failwith("TODO: collectBracketElements")

/* TODO: buildForm — THE MAIN FUNCTION
   Pattern-match on (left, leftUf, closed, rightUf, right) and dispatch:

   1. Bracket forms (no left/right, closed ends with ")" or "]"):
      - Use collectBracketElements to get element groups
      - Parens with one element: set parens=true on metadata
      - Parens with multiple: build nested Comma nodes, set parens=true
      - Brackets: build List, or Cons if last element is a spread (...)

   2. Atoms (no left/right, CHead with TAtom):
      - Hole, Identifier, StringLit

   3. Keyword constructs (CMatch with "fun" or "let" head):
      - fun(pat)=> : interior is pattern, right child is body => Fun
      - let(binding)in : interior is binding, right child is body => Let

   4. Infix operators (CHead with TNamed):
      - ":" => Asc
      - "->" => Arrow
      - "=" => Eq
      - Named atom (no children) => Identifier
      - Any other named token => BinOp (catch-all)

   5. Match chains (ends with "end", isMatchChain):
      - Dispatch to buildMatchChain

   6. If chains (ends with "end", isIfChain):
      - Dispatch to buildIfChain

   7. Other blocks (ends with "end"):
      - Dispatch to buildBlocks

   8. Catch-all => BuilderError *)
and buildForm = (_form: openForm): term =>
  failwith("TODO: buildForm")

/* TODO: buildMatchChain
   Extract scrutinee and branches via collectMatchBranches,
   then produce Match(scrutinee, branches). */
and buildMatchChain = (_cf: closedForm): term =>
  failwith("TODO: buildMatchChain")

/* TODO: buildUnform
   Convert a single unform to a list of terms.
   - USecondary(_) => [] (whitespace/comments produce nothing)
   - UShard(token) => [localize(mk(Shard(token.value)), token)] *)
and buildUnform =
  fun
  | _ => failwith("TODO: buildUnform")

/* TODO: buildUnforms
   Concatenate buildUnform results for a list of unforms. */
and buildUnforms = _unforms =>
  failwith("TODO: buildUnforms")

/* TODO: buildSharded
   Convert a sharded item to a list of terms.
   - Unform(u) => buildUnform(u)
   - Form(f) => [buildForm(f)] */
and buildSharded =
  fun
  | _ => failwith("TODO: buildSharded");

/* TODO: build
   Top-level entry point. Takes the parser output (list of sharded open forms)
   and produces a single term by calling buildTerms. */
let build = (_forms: list(sharded(openForm))): term =>
  failwith("TODO: build");
