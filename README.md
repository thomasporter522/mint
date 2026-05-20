# The Mint Proof System

Mint's design is centered around the virtue of _objectivity_. That is, the semantics should be easily read off of the syntax, with as little semantic obfuscation and variation as possible. To that end, the object-level language is built from dependently typed term formers. Every term former must be postulated or constructed; none are built in.

## Getting Started

- Run `make init`. 
- Run `make vscode-init`. 
- Run `make vscode-install`. 
- (Re)start VSCode, and open a file in `mint/examples`.

## Future Directions

- Elaboration should be persisted in the buffer (maybe folded and gray), not just ghostly.
- Separate what is elided (irrelevant/uniquely determined) from what's merely ghostly (the result of elaboration).
- Inserted code can be hierarchically marked for progressive unfolding.  
- User-written construct-block completion procedures.
- User-written normalization procedures.
- User-defined syntax (unicode, mixfix?)
- A module-like system for reusable, nested hypothetical reasoning.

## Minor TODOs

- ML features: multi-pattern `fun`, destructuring `let`. 
- Interdependent signatures, e.g. `postulate \ A : B \ B : A`. 
- Go to definition for schemas. 

## Issues

- Unreadable inconsistency messages when parameters are explicit
     - Pretty print can greedily, iteratively, recursively remove arguments until it doesn't typecheck

## Future case studies
- Natural number game
- Mathematics in Lean, Avigad
- Gauge types
- Quotient Inductive Types from HoTT
- PLFA/Software Foundations
- POPLMark