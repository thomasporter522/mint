# The Mint Proof System

Mint's design is centered around the virtue of _objectivity_. That is, the semantics should be easily read off of the syntax, with as little semantic obfuscation and variation as possible. To that end, the object-level language is built from dependently typed term formers. Every term former must be postulated or constructed; none are built in.

## Getting Started

- Run `make init`. 
- Run `make vscode-init`. 
- Run `make vscode-install`. 
- (Re)start VSCode, and open a file in `mint/examples`.

## Future Directions

- Move to typed abstract binding trees rather than typed abstract syntax trees.
- Elaboration should be persisted in the buffer (maybe folded and gray), not just ghostly.
- Inserted code can be hierarchically marked for progressive unfolding.  
- User-written conversion and normalization procedures.
- A module-like system for reusable, nested hypothetical reasoning.

## Minor TODOs

- If implicit arguments are not solved, they shouldn't be expanded inline. 
- Ellipses should take up an existing space when possible, rather than creating a new one. 
- ML features: multi-pattern `fun`, destructuring `let`. 
- Interdependent signatures, e.g. `postulate \ A : B \ B : A`. 
- Go to definition for schemas. 

## Bugs

- Unification conflicts should be localized to the hole, not the contracticting unification site.

## Issues

- Unreadable inconsistency messages when parameters are explicit
     - Pretty print can greedily, iteratively, recursively remove arguments until it doesn't typecheck
- Expected type isn't propagated from signature to body in abstractions when using heterogeneous equality
- It's annoying to add parens around single identifers with fully inferred args