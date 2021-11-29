# tinka-hs

Dependently typed programming language written in Haskell.
Code is based on https://github.com/AndrasKovacs/elaboration-zoo .

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
- predicative non-cumulative hierarchy of universes, with a lifting operator for globals and Lift for non-globals
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
- [x] parser for sigma types
- [x] parser for pairs
- [x] parser for simple projections (fst, snd)
- [x] some base types (void, unit, bool)
- [x] heterogenous equality type with axiom k
- [x] Lift, lift and lower, for simple universe lifting
- [x] simple descriptions: Desc, End, Arg and Ind and Desc elimination
- [x] descriptions fixpoint: Data, Con and Data elimination
  - [x] make some scrutinees first argument of eliminators
  - [x] add All
  - [x] add all
  - [x] add Data elimination
  - [x] add HInd
  - [x] fix universe level issues
- [x] gentle art of levitation
- [x] clean up GlobalCtx mess
- [x] get rid of ConD
- [x] add some cumulativity in elaboration
- [x] add primitive Refl
- [x] REPL
  - [x] simple imports
  - [x] handle double imports (topological sort of imports)
  - [x] do not exit REPL on module cycles
  - [x] store what file globals come from, improve duplicate global error message
- [x] metas, unification and _ solving
  - [x] typed metas
  - [x] expand elaboration to use more metas
  - [x] named holes
  - [x] show meta context when printing holes
  - [x] pruning
  - [x] universe metas
  - [x] implicit function types
    - [x] add syntax
    - [x] expand elaboration
    - [x] add parser
  - [x] add some zonking
- [x] parser for `f \x. ...`
- [x] named sigma projection
  - [x] add syntax
  - [x] add conversion checking
  - [x] add unification
  - [x] add verification
  - [x] add elaboration
  - [x] add post-fix parser
- [x] parser for unit type () and nested units []
- [x] improve core printing
- [ ] some global unfolding in holes
- [ ] improve meta handling
  - [ ] metas-as-globals if a file is elaborated
  - [ ] do not print core terms (so zonking is not necessary)
  - [ ] top-level generalization?
- [ ] improve error messages
  - [ ] avoid SomeException, use throw and throwIO
  - [ ] improve unification error messages
  - [ ] improve elaboration error message, use location info
- [ ] improve imports
  - [ ] qualified imports
- [ ] improve unification
  - [ ] postponing
- [ ] indexed datatypes
  - [ ] internal fixpoints
  - [ ] coinductive types
  - [ ] inductive-recursive types
- [ ] QTT
- [ ] instance arguments
