# Category Theory

One of the big selling points of univalent foundations over other branches of type theory, is the fact that it lends itself really well for studying category theory. In category theory, isomorphic objects are similar, which means that on paper, you can substitute one for the other. Since objects can be isomorphic to each other in multiple ways, it is nice to have a theory where objects can be equal to each other in multiple ways, because then you can try to relate isomorphism and equality, and this is precisely what happens in univalent foundations. In this tutorial we will take a look at category theory in UniMath. We will take a peek at

- [Categories](#categories)
- [Isos](#isos)
- [Functors](#functors)
- [Natural Transformations](#natural-transformations)
- [Univalence](#univalence)
- [Limits](#limits)
- [Displayed Categories](#displayed-categories)
- [Bicategories](#bicategories)

## Categories
Categories are defined in [CategoryTheory.Core.Categories](../../../UniMath/CategoryTheory/Core/Categories.v). A couple of other core concepts are defined in other files in the [Core](../../../UniMath/CategoryTheory/Core) directory. Note that [Core.Prelude](../../../UniMath/CategoryTheory/Core/Prelude.v) bundles the 5 most-used category theory files: `Categories`, `Functors`, `Isos`, `NaturalTransformations` and `Univalence`.

The definition of a category is as follows.
```coq
category              := ∑ (C : precategory),         has_homsets C.
precategory           := ∑ (C : precategory_data),    is_precategory C.
precategory_data      := ∑ (C : precategory_ob_mor),  precategory_id_comp C.
precategory_ob_mor    := ∑ (ob : UU),                 ob → ob → UU.
precategory_id_comp C :=
    ∏ c,              c --> c ×
    ∏ a b c,          a --> b → b --> c → a --> c.
is_precategory C      :=
   (∏ a b f,          identity a · f = f ×
    ∏ a b f,          f · identity b = f) ×
   (∏ a b c d f g h,  f · (g · h) = (f · g) · h ×
    ∏ a b c d f g h,  (f · g) · h = f · (g · h)).
has_homsets C         := ∏ (a b : C), isaset (a --> b).
```
Note that there is a coercion which allows us to write `C` for the objects of `C`. Also note that `a --> b` and `C⟦a, b⟧` are notation for the morphisms from `a` to `b` and that `f · g` and `g ∘ f` are notation for "`f` composed with `g`" or "`g` after `f`".

A category has the requirement that the morphisms form a set, because in that case, statements about morphisms behave better than if they do not form a set. For example, it ensures that `is_z_isomorphism` (the existence of an inverse morphism) is a mere proposition. This means that [HSET](../../../UniMath/CategoryTheory/Categories/HSET/Core.v) is a category, but [type_precat](../../../UniMath/CategoryTheory/Categories/Type/Core.v) is only a precategory.

Most of the types here have a constructor `make_...`. In addition, there is `make_is_precategory_one_assoc`, which needs only one associativity law to prove both associativity laws.

In the following example, we will turn a type with h-level 3 into a category, by taking the paths as morphisms.
```coq
Section PathCategory.

  Context (X : UU).
  Context (H : isofhlevel 3 X).

  Definition path_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact X.
      + intros a b.
        exact (a = b).
    - exact idpath.
    - intros a b c f g.
      exact (f @ g).
  Defined.

  Lemma path_is_precategory
    : is_precategory path_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f.
      reflexivity.
    - intros a b f.
      apply pathscomp0rid.
    - intros a b c d f g h.
      apply path_assoc.
  Qed.

  Lemma path_has_homsets
    : has_homsets path_precategory_data.
  Proof.
    intros a b.
    exact (H a b).
  Qed.

End PathCategory.

Definition path_category
  (X : HLevel 3)
  : category
  :=
  make_category
    (make_precategory
      (path_precategory_data X)
      (path_is_precategory X))
    (path_has_homsets _ (hlevel_property X)).
```

## Isos
In UniMath, there are two types of isomorphisms. They are defined as follows:
```coq
iso a b                   := ∑ f, is_iso f.
is_iso f                  := ∏ c, isweq (precomp_with f).
precomp_with f g          := f · g.
z_iso a b                 := ∑ f, is_z_isomorphism f.
is_z_isomorphism f        := ∑ g, is_inverse_in_precat f g.
is_inverse_in_precat f g  :=
  f · g = identity a ×
  g · f = identity b.
```
As mentioned before, in a precategory `is_z_isomorphism` is not a mere proposition, whereas `is_iso` is always a mere proposition because of the use of `isweq`. Therefore, in precategories that are not categories, `iso` is the only well-behaved type. On the other hand, `z_iso` is usually easier to work with, because it encodes the way we usually think about isomorphisms. This means, for example, that `z_iso_inv (z_iso_inv f) = f` is definitionally true, whereas `iso_inv_from_iso (iso_inv_from_iso f) = f` needs a slightly more complicated proof. Of course, in a category, the two notions are equivalent: `weq_iso_z_iso : iso b c ≃ z_iso b c`.

There is a constructor `make_z_iso` which takes in `f`, `g` and the proof that they are inverse to each other. There is also a constructor `make_z_iso'` which takes in `f` and a proof of `is_z_isomorphism f`. `is_z_isomorphism` and `is_inverse_in_precat` have the expected constructor.

To continue the example above, we will show that every morphism in our category is an isomorphism.

```coq
Definition path_category_morphism_is_iso
  {X : HLevel 3}
  {a b : path_category X}
  (f : a --> b)
  : is_z_isomorphism f.
Proof.
  use make_is_z_isomorphism.
  - exact (!f).
  - split.
    + apply pathsinv0r.
    + apply pathsinv0l.
Defined.

Definition path_category_morphism_iso
  {X : HLevel 3}
  {a b : path_category X}
  (f : a --> b)
  : z_iso a b
  := make_z_iso'
    f
    (path_category_morphism_is_iso f).
```

For `z_iso`, there are the following accessors, and some lemmas that show that they form an equivalence relation. Note that `z_iso_mor` is a coercion:

```coq
z_iso_mor               : z_iso a b → a --> b
inv_from_z_iso          : z_iso a b → b --> a
z_iso_inv_after_z_iso f : f · inv_from_z_iso f = identity a
z_iso_after_z_iso_inv f : inv_from_z_iso f · f = identity b
z_iso_comp              : z_iso a b → z_iso b c → z_iso a c
z_iso_inv               : z_iso a b → z_iso b a
identity_z_iso a        : ∏ a, z_iso a a
```
There is also an equality lemma `z_iso_eq : ∏ (i i' : z_iso a b), z_iso_mor i = z_iso_mor i' → i = i'` and its counterpart `z_iso_eq_inv`, showing that two isomorphisms are equal if their morphisms are equal.

The file [Core.Isos](../../../UniMath/CategoryTheory/Core/Isos.v) contains all manner of lemmas that can help you manipulate isomorphisms. For example:
```coq
z_iso_inv_to_left a b c f g h   : inv_from_z_iso f · h = g  → h = f · g
z_iso_inv_on_left a b c f g h   : h = f · g                 → f = h · inv_from_z_iso g
z_iso_inv_to_right a b c f g h  : f = h · inv_from_z_iso g  → f · g = h
z_iso_inv_on_right a b c f g h  : h = f · g                 → inv_from_z_iso f · h = g
cancel_z_iso f f' g             : f · g = f' · g → f = f'
cancel_z_iso' g f f'            : g · f = g · f' → f = f'
z_iso_comp_right_weq            : z_iso a b → ∏ c, b --> c ≃ a --> c
z_iso_comp_left_weq             : z_iso a b → ∏ c, c --> a ≃ c --> b
is_z_isomorphism_path           : f = f' → is_z_isomorphism f → is_z_isomorphism f'
```

## Functors
```coq
functor C C'      := ∑ (F : functor_data C C'), is_functor F.
functor_data C C' := ∑ (F : ob C → ob C'), ∏ a b, a --> b -> F a --> F b.
is_functor F      := functor_idax F × functor_compax F.
functor_idax F    := ∏ a, #F (identity a) = identity (F a).
functor_compax F  := ∏ a b c f g, #F (f · g) = #F f · #F g .
```

```coq
Coercion functor_on_objects : functor_data >-> Funclass.
Notation "# F" := (functor_on_morphisms F) (at level 3) : cat.
Notation "a ⟶ b" := (functor a b) : cat.
Notation "F ∙ G" := (functor_composite F G) : cat.
```

```coq
functor_id
functor_comp
functor_on_z_iso
reflects_morphism
functor_composite
functor_identity
constant_functor
fully_faithful
weq_ff_functor_on_z_iso
split_essentially_surjective
faithful
full
full_and_faithful
weq_fully_faithful_full_and_faithful
essentially_surjective
```

## Natural Transformations

```coq
Definition nat_trans F F'       := ∑ (t : nat_trans_data F F'), is_nat_trans F F' t.
Definition nat_trans_data F F'  := ∏ x, F x -->  F' x.
Definition is_nat_trans F F' t  := ∏ x x' f, # F f · t x' = t x · #F' f.
```

```coq
Notation "F ⟹ G" := (nat_trans F G) (at level 39) : cat.
Coercion nat_trans_data_from_nat_trans_funclass : nat_trans >-> Funclass.
```

```coq
nat_trans_ax
nat_trans_eq_weq
nat_trans_id
nat_trans_comp
```

```coq
nat_z_iso_functor_comp_assoc
```

```coq
is_nat_z_iso
nat_z_iso
```

## Univalence

```coq
Lemma is_univalent_path_category
  (X : HLevel 3)
  : is_univalent (path_category X).
Proof.
  intros a b.
  use isweq_iso.
  - exact z_iso_mor.
  - intro x.
    now induction x.
  - intro y.
    apply z_iso_eq.
    now induction (z_iso_mor y).
Qed.
```

## Limits

## Displayed Categories

## Bicategories
