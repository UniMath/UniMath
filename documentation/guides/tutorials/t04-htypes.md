# Homotopy Types

In homotopy type theory, types are regarded as spaces, where equality between terms gives paths in a space. We can try to classify the 'shapes' of these spaces, and homotopy levels are one way to do this. In this tutorial, we will take a look at

- [Contractible types](#contractible-types)
- [Mere propositions](#mere-propositions)
- [Homotopy sets](#homotopy-sets)
- [Homotopy types](#homotopy-types-1)

## Contractible types
Intuitively, a contractible type is equivalent to a single point. In particular, it does not contain 'holes' or 'loops', so whatever its shape is, it can be 'contracted' to this single point. It is defined as, `iscontr X = ∑ (x : X), (∏ y, y = x)`

In UniMath, unique existence `∃! x, Y x` is defined as `iscontr (∑ x, Y x)`.

Now if we have a proof `H : iscontr X`, there are accessors for the two parts, and a lemma
```coq
iscontrpr1 H : X.
iscontr_uniqueness H : ∏ y, y = iscontrpr1 H.
proofirrelevancecontr H : ∏ (y y' : X), y = y'.
```

Using these, we can show that any contractible type is equivalent to `unit`:
```coq
Definition iscontr_weq_unit
  {X : UU}        (* The curly braces make `X` implicit, so coq infers it from the type of H, and the signature will be `iscontr_weq_unit H` *)
  (H : iscontr X)
  : X ≃ unit.
Proof.
  use weq_iso.
  - intro x.
    exact tt.
  - intro t.
    exact (iscontrpr1 H).
  - intro x.      (* The goal is now `iscontrpr1 H = x` *)
    exact (!iscontr_uniqueness H x).
  - intro y.      (* The goal is now `tt = y` *)
    induction y.
    reflexivity.
Defined.
```

Note that the `apply` tactic is quite powerful, and can often find the right part of a ∑-type. This is not always good, but in this case, it makes the proof slightly easier:
```coq
Definition iscontr_weq_unit'
  {X : UU}
  (H : iscontr X)
  : X ≃ unit.
Proof.
  use weq_iso.
  - intro x.
    exact tt.
  - intro t.
    apply H.
  - intro x.
    symmetry.
    apply H.
  - intro y.
    induction y.
    reflexivity.
Defined.
```

If we want to show that something is contractible, there are a couple of lemmas in the library which show that a lot of the basic type formers preserve contractibility:

```coq
iscontrunit       : iscontr unit.
unique_exists     : ∏ x,  Y x → (∏ x, isaprop (Y x)) → (∏ y, Y y → y = x) → (∑ x, Y x).
iscontrfuntocontr :       iscontr Y → iscontr (X → Y).
impred_iscontr    : ∏ Y,  (∏ x, iscontr (Y x)) → iscontr (∏ x, Y x).
```

For more lemmas about contractibility, see [`Foundations/PartA`](../../../UniMath/Foundations/PartA.v) and a couple of lemmas in [`MoreFoundations/PartA`](../../../UniMath/MoreFoundations/PartA.v).

## Mere propositions
Intuitively, a mere proposition is a space which may or may not be inhabited, and its inhabitance is the only 'information'. `X` is a mere proposition if, for all `x y : X`, the type `x = y` is contractible.

In UniMath, a type and the proof that it is a proposition are sometimes bundled together, into a term of `hProp`, which is defined as `∑ X, isaprop X`. There is a coercion `hProptoType : hProp -> UU` and an accessor `propproperty : ∏ (X : hProp), isaprop X`.

If we have `H : isaprop X`, we have a lemma `proofirrelevance X H : ∏ (x y : X), x = y`, although `apply H` often works too (or `apply propproperty` for `X : hProp`).

Like with `iscontr`, there are some lemmas about under what circumstances the different type formers give a proposition. Note in particular `isapropifcontr`, which shows that a contractible type is also a proposition:

```coq
isapropempty        : isaprop empty.
isapropifcontr      : iscontr X → isaprop X.
isapropdirprod      : ∏ X Y,  isaprop X → isaprop Y → isaprop (X × Y).
isaproptotal2       : ∏ Y,    isPredicate Y → (∏ x y, Y x → Y y → x = y) → isaprop (∑ x, Y x).
isapropimpl         : ∏ X Y,  isaprop Y → isaprop (X → Y).
impred_isaprop      : ∏ Y,    (∏ x, isaprop (Y x)) → isaprop (∏ x, Y x).
invproofirrelevance : ∏ X, (∏ (x y : X), x = y) → isaprop X.
```

For example, we can define a proposition that characterizes when a number is infinite:
```coq
Definition is_infinite
  (m : nat)
  : UU
  := ∏ (n : nat), n < m.

Lemma isaprop_is_infinite
  (m : nat)
  : isaprop (is_infinite m).
Proof.
  apply impred_isaprop.
  intro n.
  unfold natlth.
  unfold natgth.    (* `n < m` is defined as `natgtb m n = true` *)
  apply isasetbool. (* Since bool is a set, any two equality proofs in bool are the same *)
Qed.
```

For more lemmas about propositions, see [`Foundations/PartB`](../../../UniMath/Foundations/PartB.v) and [`(More)Foundations/Propositions`](../../../UniMath/Foundations/Propositions.v).

### The propositional truncation
For all types `X`, there is a mere proposition `∥ X ∥`, which means '`X` is inhabited'. Its underlying type is defined as `∏ (P : hProp), ((X -> P) -> P)`. It has a constructor `hinhpr : X → ∥ X ∥`.

It has (by definition) a universal property `hinhuniv`, which says that if we have `x : ∥ X ∥` in our context, and our goal is a mere proposition `P`, we can assume that we have `x : X` instead. There are related lemmas: `factor_through_squash`, which allows `P : UU`, but requires a separate proof of `isaprop P`; Or `hinhfun`, which gives a function `∥ X ∥ → ∥ Y ∥` from a function `X → Y`.

In UniMath, existence `∃ x, Y x` is defined as `∥ ∑ x, Y x ∥`.

In the following toy example, we will define what it means for a number to be (in)finite, and show that a finite number is not infinite.
```coq
Definition is_finite
  (m : nat)
  : UU
  := ∥ ∑ (n : nat), m ≤ n ∥.

Lemma nat_is_finite
  (m : nat)
  : is_finite m.
Proof.
  apply hinhpr.       (* This changes the goal to ∑ n, m ≤ n *)
  exists m.           (* This changes the goal to m ≤ m *)
  apply isreflnatleh.
Qed.

Lemma is_finite_to_is_not_infinite
  (m : nat)
  : is_finite m → ¬ (is_infinite m).
Proof.
  (* `¬ P` is defined as `P → ∅`, so by introducing `Hi`, the goal becomes `∅` *)
  intros Hf Hi.
  (* The revert tactic puts Hf back into the goal, so the goal becomes `is_finite m → ∅`. *)
  revert Hf.
  (* Applying `factor_through_squash` splits the goal into `isaprop empty` and `(∑ n, m ≤ n) → ∅` *)
  apply factor_through_squash.
  - exact isapropempty.
  - intro Hf.
    (* We will use a lemma which says that we cannot have `pr1 Hf < m` and `pr1 Hf ≥ m` at the same time *)
    apply (natlthtonegnatgeh (pr1 Hf) m).
    + apply Hi.
    + apply Hf.
Qed.
```

## Homotopy sets
Intuition

`X` is a set, if all the path types `x = y` are mere propositions. If this is the case, `X` behaves like a set in set theory, where equality 'does not carry additional information'.

`hSet`

```coq
isasetbool      : isaset bool.
isasetnat       : isaset nat.
isasetaprop     : isaprop X → isaset X.
isasetcoprod    : ∏ X Y,  isaset X → isaset Y → isaset (X ⨿ Y).
isaset_dirprod  :         isaset X → isaset Y → isaset (X × Y).
isaset_total2   : ∏ Y,    isaset X → (∏ x, isaset (Y x)) → isaset (∑ x : X, P x).
funspace_isaset :         isaset Y → isaset (X → Y)
impred_isaset   : ∏ Y,    (∏ x, isaset (Y x)) → isaset (∏ x, Y x).
```

`setproperty` and `homset_property` can close a lot of goals

Accessors

### Predicates and subsets
Now, a predicate, which has been mentioned previously, is defined as a function `P : X → UU` such that `∏ x, isaprop (P x)`. A predicate is equivalent to a `hsubtype`, which is defined as a function `X → hProp`.

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
