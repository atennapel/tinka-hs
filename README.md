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
- predicative non-cumulative hierarchy of universes, with simple universe polymorphism
- "Gentle art of Levitation"-style descriptions

For example:
```
Sum : Type -> Type -> Type
  = \A B. (b : Bool) ** (elim Bool 1) (\_. Type) A B b;

Left : (A B : Type) -> A -> Sum A B
  = \A B x. (True, x);

Right : (A B : Type) -> B -> Sum A B
  = \A B x. (False, x);

indSum :
  (A B : Type)
  (P : Sum A B -> Type)
  (left : (x : A) -> P (Left A B x))
  (right : (x : B) -> P (Right A B x))
  (sum : Sum A B)
  -> P sum
  = \A B P left right sum.
    (elim Bool) (\b. (x : (elim Bool 1) (\_. Type) A B b) -> P (b, x)) left right (fst sum) (snd sum);
```

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
  - [ ] primitives
  - [ ] globals
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
