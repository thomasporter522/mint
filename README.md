# The Mint Proof System

Mint's design is centered around the virtue of _objectivity_. That is, the semantics should be easily read off of the syntax, with as little semantic obfuscation and variation as possible. To that end, the object-level language is built from dependently typed term formers. Every term former must be postulated or constructed; none are built in.

## Getting Started

- Run `make init` the first time building. 
- Run `make`. 

## Future Directions

- Automatic inference of missing arguments to term constructors.
- User-written conversion procedures.
- A module-like system for reusable, nested hypothetical reasoning.
