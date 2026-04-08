# Meta Language Design

The ML extends the OL (object language) with standard functional programming
constructs. The OL is a subset of the ML — OL terms are ML values of type `Term`.

## Key principles

- `?` is purely ML-level: binds in patterns, represents holes/metas in expressions.
- In patterns, the first occurrence of `?x` binds; subsequent `?x` in the same
  pattern means "must equal the already-bound `x`" (equality constraint).
- In expressions, pattern-bound variables are used without `?` — they're just
  regular ML variables.
- OL terms are just identifiers and application. No ascription, no patterns, no meta-variables.
- Unquoted identifiers resolve from the combined OL+ML scope.
- Schemas always have type `List Signature -> Result (List Term)` (implicit from `schema` keyword).
- `Signature` is an alias for `(List (String, Term), Term)` — parameter list + return type.

## Grammar

```
(* ===== Object Language terms ===== *)

term     ::= ident
           | term term
           | (term)

(* ===== Meta Language expressions ===== *)

expr     ::= term
           | ?ident                       (* meta-variable / hole *)
           | let pat = expr in expr
           | fun pat => expr
           | match expr with branches
           | if expr then expr else expr
           | expr binop expr
           | [expr, ..., expr]            (* list literal *)
           | (expr, expr)                 (* pair *)
           | Ok expr | Error str          (* result constructors *)
           | str                          (* string literal *)

branches ::= | pat => expr { | pat => expr }

(* ===== Patterns ===== *)

pat      ::= ?ident                       (* binding / equality constraint *)
           | _                            (* wildcard *)
           | ident pat*                   (* OL constructor + sub-patterns *)
           | [pat, ..., pat]              (* list pattern *)
           | (pat, pat)                   (* pair pattern *)
           | str                          (* string literal pattern *)

(* ===== Types ===== *)

type     ::= Term | Sort | String
           | List type | Result type
           | (type, type)                 (* pair *)
           | type -> type
           | (type)

(* ===== Type aliases ===== *)
(* Signature = (List (String, Term), Term)  — params + return type *)
```

## Example

A schema that checks "definition" blocks (two declarations where the second
is an equality proof):

```
schema definition : List Signature -> Result (List Term) =
  fun s => match s with
  | [([(?x, ?t)], ?ret),
     ([(?x_eq, eq ?t ?t ?body)], _)]
      => Ok [body, refl t body]
  | _ =>
    if List.length s != 2
    then Error "definition declarations must have length 2"
    else Error "invalid declaration"
```

## Usage in the OL

```
postulate
...
end

schema definition = ...

construct by definition
  x : T
  x_eq : eq T T x proof
end
```

The `construct by definition` block passes its declaration signatures to the
`definition` schema, which validates them and returns the terms to bind.
