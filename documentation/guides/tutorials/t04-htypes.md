# Homotopy Types

In homotopy type theory, types are regarded as spaces, where equality between terms gives paths in a space. We can try to classify the 'shapes' of these spaces, and homotopy levels are one way to do this. In this tutorial, we will take a look at

- [Contractible types](#contractible-types)
- [Mere propositions](#mere-propositions)
  - [The propositional truncation](#the-propositional-truncation)
- [Homotopy sets](#homotopy-sets)
  - [Predicates and subsets](#predicates-and-subsets)
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
iscontr_prod	  : ∏ X Y, iscontr X → iscontr Y → iscontr (X × Y).
impred_iscontr    : ∏ Y,  (∏ x, iscontr (Y x)) → iscontr (∏ x, Y x).
```

For more lemmas about contractibility, see [`Foundations/PartA`](../../../UniMath/Foundations/PartA.v) and a couple of lemmas in [`MoreFoundations/PartA`](../../../UniMath/MoreFoundations/PartA.v).

## Mere propositions
A mere proposition is a type which may or may not be inhabited, and its inhabitance is the only 'information'. `X` is a mere proposition if, for all `x y : X`, the type `x = y` is contractible.

In UniMath, a type and the proof that it is a proposition are sometimes bundled together, into a term of `hProp`, which is defined as `∑ X, isaprop X`. There is a coercion `hProptoType : hProp -> UU`, an accessor `propproperty : ∏ (X : hProp), isaprop X` and a constructor `make_hProp X H : hProp`.

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
  apply isasetbool. (* Since bool is a set, equality in bool is a proposition *)
Qed.
```

For more lemmas about propositions, see [`Foundations/PartB`](../../../UniMath/Foundations/PartB.v) and [`(More)Foundations/Propositions`](../../../UniMath/Foundations/Propositions.v).

### The propositional truncation
For all types `X`, there is a mere proposition `∥ X ∥`, which means '`X` is inhabited'. Its underlying type is defined as `∏ (P : hProp), ((X -> P) -> P)`. It has a constructor `hinhpr : X → ∥ X ∥`.

It has (by definition) a universal property `hinhuniv`, which says that if we have `x : ∥ X ∥` in our context, and our goal is a mere proposition `P`, we can assume that we have `x : X` instead. There are related lemmas: `factor_through_squash`, which allows `P : UU`, but requires a separate proof of `isaprop P`. The lemma `hinhfun` gives a function `∥ X ∥ → ∥ Y ∥` from a function `X → Y`.

In UniMath, "There exists `x : X` such that `Y x`", denoted as `∃ x, Y x`, is defined as `∥ ∑ x, Y x ∥`.

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
`X` is a set if all the path types `x = y` are mere propositions. If this is the case, `X` behaves like a set in set theory, where equality 'does not carry additional information'.

Often, the type `X`, and the property `H : isaset X` are bundled together in a type `hSet = ∑ X, isaset X`. It has a coercion `pr1hSet: hSet -> UU`, an accessor `setproperty X : isaset X` and a constructor `make_hSet X i : hSet`.

Again, being a set is preserved by most of the standard type constructions:
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

In practice, there are a lot of goals of the form `p = q`, where both `p` and `q` will have type `x = y` with `x y : X` and `X : hSet`. In such a case, `apply setproperty` will close the goal. When working with categories, `apply homset_property` will close the goal `p = q` with `p q : f = g` where `f` and `g` are morphisms in a category.

For more lemmas about sets, see [`Foundations/PartB`](../../../UniMath/Foundations/PartB.v) and [`(More)Foundations/Sets`](../../../UniMath/Foundations/Sets.v).

### Predicates and subsets
Now, we can define a predicate, which has been mentioned previously, as a function `P : X → UU` such that `∏ x, isaprop (P x)`. This is equivalent to a `hsubtype`, which is defined as a function `X → hProp`. Such a function `P : hsubtype X` gives rise to a type `carrier X := ∑ x, P x`. If `X` is a set, then we get a set `carrier_subset P`.

For example, we can define the set of all decidable propositions:
```coq
(* A proposition is decidable if we have a proof of either the proposition, or of its negation *)
Definition is_decidable
  (X : hProp)
  : UU
  := X ⨿ (X → ∅).

Lemma isaprop_is_decidable
  (X : hProp)
  : isaprop (is_decidable X).
Proof.
  (* A coproduct of two propositions is a propositions if the propositions exclude each other *)
  apply isapropcoprod.
  (* X is a proposition *)
  - apply propproperty.
  (* (X → ∅) is a proposition *)
  - apply isapropimpl.
    apply isapropempty.
  (* X and (X → ∅) never hold at the same time *)
  - intros p q.
    apply q.
    apply p.
Qed.

Definition decidable_hProp
  : hSet.
Proof.
  use carrier_subset.
  - use make_hSet.
    (* Our base type is the type of propositions *)
    + exact hProp.
    (* The propositions form a set *)
    + exact isasethProp.
  - intro X.
    use make_hProp.
    (* Our subtype is given by decidability of the propositions *)
    + exact (is_decidable X).
    (* And decidability is a proposition *)
    + apply isaprop_is_decidable.
Defined.
```

## Homotopy types

In general, if `X` is contractible, it is of 'hlevel' 0. If all path types of `X` are of h-level `n`, `X` is of h-level `S n`.

There is a geometric intuition behind all this: A space is of h-level n if it has no holes of dimension greater than or equal to n-1. That is, any sphere with dimension greater than or equal to n-1 in it can be filled to a disc:
- If a space has h-level 2, it has no holes of dimension 1 (or greater), which means that no component has loops and it is a disjoint union of contractible components - so essentially a discrete set.
- A 0-dimensional sphere is just two points, and a disc filling it is a line between them; so a '0-dimensional hole' is two points that cannot be joined by a path, and so a space has h-level 1 if it is essentially discrete and also has at most one component.
- A "-1-dimensional sphere" is the empty space, and the disc filling it is a point, so a "-1-dimensional hole" is an uninhabited void. Therefore, a space has h-level 0 if besides being essentially discrete and connected, it’s also non-empty - which comes out equivalent to being contractible.
- For higher dimensions, the geometric intuition is fairly clear. For example, a space with h-level 3 can have loops, but cannot have 2-dimensional holes (like "bubbles") or higher.

We have general versions of the lemmas about contractible types, propositions and sets that we saw before:
```coq
hlevelntosn         : ∏ n X,    isofhlevel n X → isofhlevel (S n) X
isofhlevelssncoprod : ∏ n X Y,  isofhlevel (S (S n)) X → isofhlevel (S (S n)) Y → isofhlevel (S (S n)) (X ⨿ Y)
isofhleveldirprod   : ∏ n X Y,  isofhlevel n X → isofhlevel n Y → isofhlevel n (X × Y).
isofhleveltotal2    : ∏ n Y,    isofhlevel n X → (∏ x, isofhlevel n (Y x)) → isofhlevel n (∑ x, Y x)
impredfun           : ∏ n X Y,  isofhlevel n Y → isofhlevel n (X → Y).
impred              : ∏ n X Y,  (∏ x, isofhlevel n (Y x)) → isofhlevel n (∏ x, Y x).
```
