# tinka-hs

Dependently typed programming language written in Haskell.
Code is based on https://github.com/AndrasKovacs/elaboration-zoo .

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
- [x] temporary parser for simple projections (fst, snd)
- [ ] parser for post-fix projections
- [ ] parser for unit type () and nested units []
- [ ] named sigma projection
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
- [ ] clean up GlobalCtx mess
- [ ] get rid of ConD?
- [ ] allow redefinition of globals?
- [ ] indexed descriptions
- [ ] metas, unification and _ solving
- [ ] implicit function types
- [ ] QTT
