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
Functors are defined as
```coq
functor C C'      := ∑ (F : functor_data C C'), is_functor F.
functor_data C C' := ∑ (F : ob C → ob C'), ∏ a b, a --> b -> F a --> F b.
is_functor F      := functor_idax F × functor_compax F.
functor_idax F    := ∏ a, #F (identity a) = identity (F a).
functor_compax F  := ∏ a b c f g, #F (f · g) = #F f · #F g .
```
Of course, there are constructors `make_functor` and `make_functor_data` (`make_is_functor` has not yet been added) and accessors `functor_id` and `functor_comp`. There is a coercion, so if `F` is a functor, you can also write `F` for the action on objects. The action on a morphism `f` has notation `# F f`. Lastly, `C ⟶ D` is notation for the type `functor C D`.

Of course, functors `F` and `G` can be composed to `F ∙ G` (notation for `functor_composite F G`) and there is an identity `functor_identity C`. There also is a constant functor `constant_functor C D X` that sends everything to `X : D`.

Note that a functor sends isos to isos: `functor_on_z_iso F a b : z_iso a b → z_iso (F a) (F b)`.

The file [Core.Functors](../../../UniMath/CategoryTheory/Core/Functors.v) defines the following properties that a functor can have:
```coq
split_essentially_surjective F  := ∏ b,     ∑ a, z_iso (F a) b
essentially_surjective F        := ∏ b,     ∃ a : C, z_iso (F a) b
fully_faithful F                := ∏ a b,   isweq (# F)
full_and_faithful F             := full F × faithful F.
full F                          := ∏ a b,   issurjective (λ f, # F f)
faithful F                      := ∏ a b,   isincl (λ f, # F f)
reflects_morphism F P           := ∏ a b f, P D (F a) (F b) (# F f) → P C a b f
```
Of course, fully faithful is equivalent to full and faithful: `weq_fully_faithful_full_and_faithful C D F : fully_faithful F ≃ full_and_faithful F`.

`reflects_morphism F P` means that `F` reflects property `P` on morphisms (i.e. if the image of a morphism satisfies `P`, the original morphism satisfies `P`). For example, a fully faithful functor reflects isomorphisms, which actually gives an equivalence: `weq_ff_functor_on_z_iso : fully_faithful F → ∏ a b, z_iso a b ≃ z_iso (F a) (F b)`.

In the following extensive example, we will construct a functor from the path category of `X` to its opposite category, which flips all the paths. We will show that it is fully faithful and split essentially surjective.

```coq
Definition path_category_involution_functor_data
  (X : HLevel 3)
  : functor_data (path_category X) (path_category X)^op.
Proof.
  use make_functor_data.
  - intro x.
    exact x.
  - intros a b f.
    exact (!f).
Defined.

Lemma path_category_involution_is_functor
  (X : HLevel 3)
  : is_functor (path_category_involution_functor_data X).
Proof.
  split.
  - intro x.
    reflexivity.
  - intros x y z.
    exact pathscomp_inv.
Qed.

Definition path_category_involution
  (X : HLevel 3)
  : path_category X ⟶ (path_category X)^op
  := make_functor
    (path_category_involution_functor_data X)
    (path_category_involution_is_functor X).

Definition path_category_involution_essentially_surjective
  (X : HLevel 3)
  : split_essentially_surjective (path_category_involution X).
Proof.
  intro x.
  exists x.
  exact (identity_z_iso x).
Defined.

Definition path_category_fully_faithful
  (X : HLevel 3)
  : fully_faithful (path_category_involution X).
Proof.
  intros x y.
  use isweq_iso.
  - intro f.
    exact (!f).
  - exact pathsinv0inv0.
  - exact pathsinv0inv0.
Defined.
```

## Natural Transformations
Natural transformations between functors `F` and `F'` are defined as
```coq
Definition nat_trans F F'       := ∑ (t : nat_trans_data F F'), is_nat_trans F F' t.
Definition nat_trans_data F F'  := ∏ x, F x -->  F' x.
Definition is_nat_trans F F' t  := ∏ x x' f, # F f · t x' = t x · #F' f.
```

Again, there is a constructor `make_nat_trans`, a coercion from `nat_trans` to `nat_trans_data` and an accessor `nat_trans_ax` for the property. The type `nat_trans F G` is denoted `F ⟹ G`.

Transformations `f : F ⟹ G` and `g : G ⟹ H` can be composed to `nat_trans_comp F G H f g` and there is an identity `nat_trans_id F : F ⟹ F`.

Equality between natural transformation is determined by equality on its data: `nat_trans_eq_weq : has_homsets D → ∏ F G f g, f = g ≃ (∏ c, f c = g c)`. Note that there is a lemma `nat_trans_eq_alt : ∏ F F' f g, (∏ c, f c = g c) → f = g` which assumes that `D` is a category instead of a precategory, so it does not need `has_homsets D` separately.

There is a category `[C, D]` (notation for `functor_category C D`), defined in [CategoryTheory.FunctorCategory](../../../UniMath/CategoryTheory/FunctorCategory.v), where the objects are functors `C ⟶ D` and the morphisms are natural transformations. This means, of course, that there is a notion of isomorphism `F ≅ G` between functors.

There is also a special notion of isomorphism of functors, which is called a 'natural isomorphism', defined in [Core.NaturalTransformations](../../../UniMath/CategoryTheory/Core/NaturalTransformations.v) as a natural transformation that also is a pointwise isomorphism:
```coq
nat_z_iso C D F G       := ∑ (f : F ⟹ G), is_nat_z_iso μ
is_nat_z_iso C D F G f  := ∏ c, is_z_isomorphism (f c)
```

Of course, they are equivalent, as shown in [CategoryTheory.FunctorCategory](../../../UniMath/CategoryTheory/FunctorCategory.v) in the lemma `z_iso_is_nat_z_iso F G : z_iso F G ≃ nat_z_iso F G`.

For example, we can show that when we compose the involution functor from the previous example with its opposite (`C ⟶ C^op ⟶ C^op^op = C`), the result is isomorphic to the identity functor:
```coq
Definition path_category_involution_nat_iso
  (X : HLevel 3)
  : nat_z_iso
    (path_category_involution X ∙ functor_opp (path_category_involution X))
    (functor_identity (path_category X)).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + intro x.
      exact (idpath x).
    + intros x y f.
      refine (pathscomp0rid _ @ _).
      exact (pathsinv0inv0 f).
  - intro x.
    apply (is_z_isomorphism_identity x).
Defined.

Definition path_category_involution_iso
  (X : HLevel 3)
  : z_iso (C := [path_category X, path_category X])
    (path_category_involution X ∙ functor_opp (path_category_involution X))
    (functor_identity (path_category X))
  := invmap
    (z_iso_is_nat_z_iso (D := path_category X) _ _)
    (path_category_involution_nat_iso X).
```

Lastly, there is a somewhat noteworthy lemma `nat_z_iso_functor_comp_assoc F1 F2 F3 : nat_z_iso (F1 ∙ (F2 ∙ F3)) ((F1 ∙ F2) ∙ F3)`, showing associativity of functor composition as a natural isomorphism.

## Univalence
The univalent category is a core definition in univalent foundations. It is a category where isomorphism is equivalent to equality:
```coq
idtoiso C a b   := paths_rect C a (λ c _, z_iso a c) (identity_z_iso a) b
is_univalent C  := ∏ a b, isweq idtoiso
```
Note that `idtoiso` is defined using path induction.

When working with univalent categories, the property `H : is_univalent C` is often handled separately from `C : category`. Still, in some cases, they are packaged together as an instance of `univalent_category := ∑ (C : category), is_univalent C`. For those cases, there is a constructor `make_univalent_category`, as well as a coercion from `C : univalent_category` to `C : category`, and an accessor `univalent_category_is_univalent C : is_univalent C`.

The following definitions expose the different parts of the equivalence:
```coq
isotoid C                 : is_univalent C → z_iso a b → a = b
idtoiso_isotoid C H a b f : idtoiso (isotoid C H f) = f
isotoid_idtoiso C H a b p : isotoid C H (idtoiso p) = p
```

Now, [Core.Univalence](../../../UniMath/CategoryTheory/Core/Univalence.v) has an interesting lemma about the structure of the object type of a univalent category, as well as a lot of lemmas about the behaviour of `idtoiso` and `isotoid`. For example:
```coq
univalent_category_has_groupoid_ob  : ∏ (C : univalent_category), isofhlevel 3 C
inv_isotoid C H a b f               : ! isotoid C H f = isotoid C H (z_iso_inv_from_z_iso f)
isotoid_comp C H a b c f g          : isotoid C H (z_iso_comp e f) = isotoid C H e @ isotoid C H f
transportf_isotoid C H a a' b f g   : transportf (λ c, C ⟦ c, b ⟧) (isotoid C H f) g = inv_from_z_iso f · g
transportf_isotoid' C H a b b' f g  : transportf (λ c, C ⟦ a, c ⟧) (isotoid C H f) g = g · f
```

For many standard category constructions, univalence of one component gives univalence of the category, like a functor category ([`is_univalent_functor_category`](../../../UniMath/CategoryTheory/FunctorCategory.v)), a (co)slice category ([`is_univalent_slicecat`](../../../UniMath/CategoryTheory/slicecat.v)), a full subcategory ([`is_univalent_full_sub_category`](../../../UniMath/CategoryTheory/Subcategory/Full.v)) and an opposite category ([`op_is_univalent`](../../../UniMath/CategoryTheory/opp_precat.v)).

Now, we can show that the path category from the example is univalent, since `idtoiso` effectively sends a path `p` to `(p, !p, pathsinv0r p, pathsinv0l p)`. From this, we can deduce that the functor category between `path_category X` and itself is univalent, and we can conclude that the isomorphism which we showed earlier, is in fact an equality:
```coq
Lemma is_univalent_path_category
  (X : HLevel 3)
  : is_univalent (path_category X).
Proof.
  intros a b.
  use isweq_iso.
  - exact z_iso_mor.
  - intro x.
    induction x.
    reflexivity.
  - intro y.
    apply z_iso_eq.
    induction (z_iso_mor y).
    reflexivity.
Qed.

Lemma involution_is_involution
  (X : HLevel 3)
  : path_category_involution X ∙ functor_opp (path_category_involution X)
  = functor_identity (path_category X).
Proof.
  use (isotoid _ _ (path_category_involution_iso X)).
  apply is_univalent_functor_category.
  apply is_univalent_path_category.
Qed.
```

## Limits

## Displayed Categories

## Bicategories
