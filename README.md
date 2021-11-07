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

Currently supports only pi-types and a predicative non-cumulative hierarchy of universes, with a lifting operator for globals.
For example:
```
Nat : Type1 = (A : Type) -> A -> (A -> A) -> A;
Z : Nat = \A z s. z;
S : Nat -> Nat = \n A z s. s (n A z s);

Nat1 : Type2 = Nat^;
Nat99 : Type100 = Nat^99;
```

TODO:
- [ ] parser for sigma types
- [ ] named sigma projection
- [x] some base types (void, unit, bool)
- [x] heterogenous equality type with axiom k
- [ ] descriptions with a fixpoint
- [ ] Lift, lift and lower, for simple univere lifting
- [ ] implicit function types
- [ ] QTT
