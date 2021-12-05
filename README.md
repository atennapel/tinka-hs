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
  - [ ] globals
  - [ ] holes
- [ ] REPL
- [ ] definitions
- [ ] modules
- [ ] sigmas
- [ ] primitives
- [ ] metas
  - [ ] unification
  - [ ] holes
  - [ ] zonking
- [ ] level metas
- [ ] implicit functions
  - [ ] update syntax
  - [ ] update elaboration
- [ ] update unification
  - [ ] pruning
  - [ ] postponing
