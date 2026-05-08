# The Mint Proof System

Mint's design is centered around the virtue of _objectivity_. That is, the semantics should be easily read off of the syntax, with as little semantic obfuscation and variation as possible. To that end, the object-level language is built from dependently typed term formers. Every term former must be postulated or constructed; none are built in.

## Getting Started

- Run `make init`. 
- Run `make vscode-init`. 
- Run `make vscode-install`. 
- (Re)start VSCode, and open a file in `mint/examples`.

## Future Directions

- Automatic inference of missing arguments to term constructors.
- User-written conversion procedures.
- A module-like system for reusable, nested hypothetical reasoning.

## Minor TODOs

- Schema errors should be localized to schema reference, not first line of construction
- Object-level identifiers should inhabit an abstract type from the perspective of the meta-level code
- Warnings for shadowing
- Expose context to schemas