# tinka-hs

Dependently typed programming language written in Haskell.
Code is based on https://github.com/AndrasKovacs/elaboration-zoo and https://gist.github.com/AndrasKovacs/d5d78d8e556d91afb1f724d1c2246b6b.

Start REPL
```
stack run repl
```

Elaborate an expression
```
stack run < expr.txt
```

Elaborate definitions
```
stack run elab-defs < defs.txt
```

Currently supports:
- pi-types
- sigma-types
- Void, Unit, Bool primitive types
- heterogenous equality type with axiom K
- predicative non-cumulative hierarchy of universes, with simple universe polymorphism
- "Gentle art of Levitation"-style descriptions

TODO:
- [x] core language
  - [x] syntax
  - [x] levels
  - [x] values
  - [x] verification
- [x] surface language
  - [x] syntax
  - [x] parser
  - [x] elaboration
  - [x] primitives
  - [x] holes
  - [x] globals
- [x] definitions
- [x] modules
- [x] metas
  - [x] unification
  - [x] zonking
  - [x] update elaboration
  - [x] named holes
  - [x] implicit functions
- [ ] level metas
  - [x] basic level metas
  - [x] levels in pi/sigma
  - [x] update elaboration
  - [ ] lam and app with level renaming
  - [ ] improve level unification
- [ ] descriptions
  - [x] Desc and Data constructors
  - [x] Ex and El
  - [ ] bidirectional Con
  - [ ] Data elimination
  - [ ] levitation
- [ ] update unification
  - [ ] eta rule for Bool
  - [ ] pruning
  - [ ] postponing
- [ ] add more syntax
  - [ ] if syntax
  - [ ] equality syntax
- [ ] improve error message
  - [ ] use source position
- [ ] more types
  - [ ] nested fixpoints
  - [ ] coinductive types
  - [ ] mixed fixpoints
  - [ ] nested types
  - [ ] inductive-recursive types
  - [ ] inductive-inductive types
  - [ ] curried indexes and parameters
- [ ] Prop universe
- [ ] Setoid type theory/observational type theory

Level solver issues:
- max '4 ?l7 ~ S '4
