# Equivalences

In this tutorial, we will take a look at so-called 'weak equivalences' between types. We will look at

- [Using a weak equivalence](#using-a-weak-equivalence)
- [Creating a weak equivalence](#creating-a-weak-equivalence)
- [Weak equivalences as an equivalence relation](#weak-equivalences-as-an-equivalence-relation)


Intuitively, an equivalence `f : X ≃ Y` consists of a function `f : X → Y` and a function `g : Y → X` such that for all `x : X` and `y : Y`, `g (f x) = x` and `f (g y) = y`, so `f` is an 'isomorphism'. Indeed, if `X` and `Y` are sets (see [tutorial 4](./t04-htypes.md)), the isomorphisms `X ≅ Y` and equivalences `X ≃ Y` are equivalent (shown in [`hset_equiv_weq_z_iso`](../../../UniMath/CategoryTheory/Categories/HSET/MonoEpiIso.v)). However, for general types `X` and `Y`, the proof that `f` is an isomorphism is not a proposition. In other words: the inverse, together with the proof that it is an inverse, is not unique. Since this is undesirable for a couple of reasons, equivalences for general types have a different definition:
```coq
Definition hfiber {X Y : UU} (f : X -> Y) (y : Y)
  : UU
  := ∑ (x : X), f x = y.

Definition isweq {X Y : UU} (f : X → Y)
  : UU
  := ∏ (y : Y), iscontr (hfiber f y).

Definition weq (X Y : UU) : UU := ∑ (f : X → Y), isweq f.
```
In other words: a weak equivalence is a function, such that every term of `Y` has a contractible preimage (the preimage consists of exactly 1 term).

## Using a weak equivalence

Weak equivalences have a couple of accessors, which allow us to treat them as isomorphisms most of the time. The accessors are
```coq
pr1weq : ∏ X ≃ Y → X → Y
invmap : ∏ X ≃ Y → Y → X
homotinvweqweq : ∏ (w : X ≃ Y) (x : X), invmap w (w x) = x
homotweqinvweq : ∏ (w : X ≃ Y) (y : Y), w (invmap w y) = y
```
In this case, `pr1weq` is a *coercion*, which means that if you have `f : X ≃ Y` and need a function, you can usually just write `f` and let coq figure out that it must use `pr1weq` to convert from an equivalence to a function.

In the following example, we transfer a binary operation, together with a proof that it is associative, along a weak equivalence:
```coq
Definition binop
  (X : UU)
  : UU
  := X → X → X.

Definition is_assoc
  (X : UU)
  (o : binop X)
  : UU
  := ∏ x y z, o (o x y) z = o x (o y z). (* Associativity means that the order of operations in x ∘ y ∘ z does not matter *)

Definition transfer_binop
  (X Y : UU)
  (f : X ≃ Y)
  : binop Y → binop X.
Proof.
  intros o x y.         (* This changes the goal to `X` *)
  apply (invmap f).     (* This changes the goal to `Y` *)
  refine (o _ _).       (* This gives the goals `Y` and `Y` *)
  - apply f.            (* This changes the goal to `X` *)
    exact x.
  - apply f.
    exact y.
Defined.

Lemma transfer_binop_is_assoc
  (X Y : UU)
  (f : X ≃ Y)
  (o : binop Y)
  : is_assoc Y o → is_assoc X (transfer_binop X Y f o).
Proof.
  intros H x y z.
  unfold transfer_binop.
  rewrite !(homotweqinvweq f).    (* This changes f (invmap f ...) to ... as many times as possible, which is two in this case *)
  apply (maponpaths (invmap f)).  (* This changes the goal to o (o (f x) (f y)) (f z) = o (f x) (o (f y) (f z)) *)
  apply H.
Qed.
```

## Creating a weak equivalence
The most basic way to construct an equivalence `X ≃ Y` is using `weq_iso`, which has the data of an isomorphism as its inputs. If `f : X → Y` has already been established and the goal is `isweq f`, there is the related lemma `isweq_iso`, which has the same inputs.
```coq
Definition coprod_swap_weq
  (X Y : UU)
  : X ⨿ Y ≃ Y ⨿ X.
Proof.
  use make_weq.
  - intro xy.                   (* This brings xy : X ⨿ Y into the context *)
    induction xy as [x | y].
    + exact (inr x).            (* We send inl x to inr x *)
    + exact (inl y).            (* We send inr y to inl y *)
  - use isweq_iso.
    + intro yx.                 (* This brings yx : Y ⨿ X into the context *)
      induction yx as [y | x].
      * exact (inr y).          (* We send inl y to inr y *)
      * exact (inl x).          (* We send inr x to inl x *)
    + intro xy.
      induction xy as [x | y];  (* This splits up the goal in a case for inl x and inr y, *)
        reflexivity.            (* Both of which are trivial *)
    + intro yx.
      induction yx as [y | x];
        reflexivity.
Defined.
```

Another common way to show `isweq f` is to use the lemma `weqhomot`, which takes as inputs some `f' : X ≃ Y`  and a proof that `f' ~ f` (notation for `homot f' f`, which means `∏ x, f' x = f x`). There is also the related lemma `isweqhomot`, where the input `f' : X ≃ Y` is split into `f' : X → Y` and `H : isweq f'`.

`weqhomot` is often used in univalence proofs: in those cases, there is a fairly simple function `f : X → Y`, but the 'simplest' way to get an equivalence `X ≃ Y` is as a complicated composition `f4 ∘ f3 ∘ f2 ∘ f1 : X ≃ W ≃ Z ≃ Y`. Then, one can show using `weqhomot` that `f` is an equivalence as well.

## Weak equivalences as an equivalence relation
Just like with paths, there is an identity equivalence `idweq X : X ≃ X` and for `f : X ≃ Y` and `g : Y ≃ Z`, we can invert `invweq f : Y ≃ X` and compose `(g ∘ f)%weq : X ≃ Z` (which is notation for `weqcomp f g`).
