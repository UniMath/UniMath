# Homotopy Types

In homotopy type theory, types are regarded as spaces, where equality between terms gives paths in a space. We can try to classify the 'shapes' of these spaces, and homotopy levels are one way to do this. In this tutorial, we will take a look at

- [Contractible types](#contractible-types)
- [Mere propositions](#mere-propositions)
- [Homotopy sets](#homotopy-sets)
- [Homotopy types](#homotopy-types-1)

## Contractible types
Intuitively, a contractible type is equivalent to a single point. It may consist of multiple points that are connected to each other, but it does not contain 'holes' or 'loops'. It is defined as, `iscontr X = ∑ (x : X), (∏ y, y = x)`

<!-- No iscontrdirprod? -->

```coq
iscontrunit       : isofhlevel 0 unit.
unique_exists     : ∏ x,  Y x → (∏ x, isaprop (Y x)) → (∏ y, Y y → y = x) → (∑ x, Y x).
iscontrfuntocontr :       iscontr Y → iscontr (X → Y).
impred_iscontr    : ∏ Y,  (∏ x, iscontr (Y x)) → iscontr (∏ x, Y x).
```

`∃! _, _ = iscontr ∑ _, _`

Accessors

## Mere propositions
Intuition

`X` is a mere proposition if, for all `x y : X`, the type `x = y` is contractible.

`hProp`

```coq
isapropempty    : isofhlevel 1 empty.
isapropifcontr  :         iscontr X → isaprop X.
isapropdirprod  : ∏ X Y,  isaprop X → isaprop Y → isaprop (X × Y).
isaproptotal2   : ∏ Y,    isPredicate Y → (∏ x y, Y x → Y y → x = y) → isaprop (∑ x, Y x).
isapropimpl     : ∏ X Y,  isaprop Y → isaprop (X → Y).
impred_isaprop  : ∏ Y,    (∏ x, isaprop (Y x)) → isaprop (∏ x, Y x).
```

Predicates / subtypes

Accessors

## Homotopy sets
Intuition

`X` is a set, if all the path types `x = y` are mere propositions. If this is the case, `X` behaves like a set in set theory, where equality 'does not carry additional information'.

`hSet`

```coq
isasetbool      : isofhlevel 2 bool.
isasetnat       : isofhlevel 2 nat.
isasetaprop     :         isaprop X → isaset X.
isasetcoprod    : ∏ X Y,  isaset X → isaset Y → isaset (X ⨿ Y).
isaset_dirprod  :         isaset X → isaset Y → isaset (X × Y).
isaset_total2   : ∏ Y,    isaset X → (∏ x, isaset (Y x)) → isaset (∑ x : X, P x).
funspace_isaset :         isaset Y → isaset (X → Y)
impred_isaset   : ∏ Y,    (∏ x, isaset (Y x)) → isaset (∏ x, Y x).
```

`setproperty` and `homset_property` can close a lot of goals

Accessors

## Homotopy types

In general, if `X` is contractible, it is of 'hlevel' 0. If all path types of `X` are of hlevel `n`, `X` is of hlevel `S n`. We have general versions of the lemmas about contractible types, propositions and sets that we saw before:
```coq
hlevelntosn         : ∏ n X,    isofhlevel n X → isofhlevel (S n) X
isofhlevelssncoprod : ∏ n X Y,  isofhlevel (S (S n)) X → isofhlevel (S (S n)) Y → isofhlevel (S (S n)) (X ⨿ Y)
isofhleveldirprod   : ∏ n X Y,  isofhlevel n X → isofhlevel n Y → isofhlevel n (X × Y).
isofhleveltotal2    : ∏ n Y,    isofhlevel n X → (∏ x, isofhlevel n (Y x)) → isofhlevel n (∑ x, Y x)
impredfun           : ∏ n X Y,  isofhlevel n Y → isofhlevel n (X → Y).
impred              : ∏ n X Y,  (∏ x, isofhlevel n (Y x)) → isofhlevel n (∏ x, Y x).
```
