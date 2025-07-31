# Category Theory

One of the big selling points of univalent foundations over other branches of type theory, is the fact that it lends itself really well for studying category theory. In category theory, isomorphic objects are similar, which means that on paper, you can substitute one for the other. Since objects can be isomorphic to each other in multiple ways, it is nice to have a theory where objects can be equal to each other in multiple ways, because then you can try to relate isomorphism and equality, and this is precisely what happens in univalent foundations. In this tutorial we will take a look at category theory in UniMath. We will take a peek at

- [Categories](#categories)
- [Isos](#isos)
- [Functors](#functors)
- [Natural Transformations](#natural-transformations)
- [Univalence](#univalence)
- [Further material](#further-material)
  - [Examples](#examples)
  - [(Co)limits](#colimits)
  - [Adjunctions](#adjunctions)
  - [Equivalences](#equivalences)
- [Displayed Categories](#displayed-categories)
  - [Some constructions](#some-constructions)
  - [Univalence](#univalence-1)
  - [Limits](#limits)
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

## Further material
In this section, we will try to give some quick pointers about what kind of material can be found where in the library.

### Examples
The package [CategoryTheory.Categories](../../../UniMath/CategoryTheory/Categories/) contains material about a lot of examples of categories, like [the category of sets](../../../UniMath/CategoryTheory/Categories/HSET/Core.v), [the category of groups](../../../UniMath/CategoryTheory/Categories/Gr.v) and [the unit category, the empty category and the category with two objects and one arrow `⊥ → ⊤`](../../../UniMath/CategoryTheory/Categories/StandardCategories.v)

### (Co)limits
Limits and colimits are described in the package [CategoryTheory.Limits](../../../UniMath/CategoryTheory/Limits/).

First of all, note that it contains [Limits.Cats](../../../UniMath/CategoryTheory/Limits/Cats/). This small package defines a diagram `d` of shape `g` in a category `C` as a functor `d : g → C`, which is very close to the pen-and-paper definition of a diagram. However, this is fairly unwieldy. For example, for a diagram, composition and identity morphisms are irrelevant and only give clutter.

Therefore, [Limits.Graphs](../../../UniMath/CategoryTheory/Limits/Graphs/) instead defines the shape of a diagram as a graph `g`, and a diagram `d` as a mapping of the nodes `v` and edges `e` to objects `dob d v` and morphisms `dmor d e` of `C`. A proof that a category has limits gives for every graph `g` and `g`-diagram `d`, a limiting cone `L : LimCone d`. Of course, `LimCone` has a constructor `make_LimCone` and accessors
```coq
lim L                     : C
limOut L v                : lim L --> dob d v
limOutCommutes L u v e    : limOut L u · dmor d e = limOut L v
limArrow L                : ∏ c (cc : cone d c), c --> lim L
limArrowCommutes L c cc v : limArrow L c cc · limOut L v = coneOut cc v
limArrowUnique L c cc     : ∏ (k : c --> lim L) (H : (∏ v, k · limOut L v = coneOut cc v)),
                              k = limArrow L c cc
```
Of note are also
```coq
limArrowEta L c           : ∏ (f : c --> lim L), f = limArrow L c ((λ v, f · limOut CC v) ,, ...)
arr_to_LimCone_eq L c f g : (∏ v, f · limOut l v = g · limOut l v) → f = g
limOfArrows L1 L2         : ∏ (f : ∏ u, dob d1 u --> dob d2 u) (H : ∏ u v e, f u · dmor d2 e = dmor d1 e · f v),
    lim L1 --> lim L2
```

Now, apart from general limits and colimits, there are all kinds of "specific" limits and colimits, like [BinaryProducts](../../../UniMath/CategoryTheory/Limits/BinProducts.v), [Equalizers](../../../UniMath/CategoryTheory/Limits/Equalizers.v) and [Cokernels](../../../UniMath/CategoryTheory/Limits/Cokernels.v). Most of these are defined twice: once [directly](../../../UniMath/CategoryTheory/Limits/BinProducts.v), and once [by defining the appropriate diagram and using the definition of general limits](../../../UniMath/CategoryTheory/Limits/Graphs/BinProducts.v). For the former, slightly less data is passed around, wheras the latter reuses more of the existing machinery. In practice, the [direct](../../../UniMath/CategoryTheory/Limits/BinProducts.v) version is almost always the preferred one.

For such a specific instance of a (co)limit, you can look for the following in its file:
- A definition both for one such limit (`BinProduct C P Q`) and for the type that denotes when the category has them all (`BinProducts C`);
- A constructor (`make_BinProduct`) and accessors (`BinProductObject`, `BinProductPr1`, `BinProductArrow`, `BinProductPr1Commutes`, `BinProductArrowUnique`) like those for general limits and their arrows;
- An equality lemma for arrows into (or out of) the (co)limit (`BinProductArrowsEq`);
- A proof that if a category has general limits, it also has this specific kind of limits (`BinProducts_from_Lims`);
- An alternative definition, about an equivalence of morphisms (`isBinProduct'`);
- A proof that two limits of the same diagram are isomorphic (`iso_between_BinProduct`);
- A proof that something isomorphic to some limit is also a limit (`iso_to_isBinProduct`).

In our running example of the path category, objects are only connected by a morphism if there is a path between them (so they are equal). This means that most limits do not exist in this category, unless `X` is contractible:
```coq
Lemma path_category_terminal_contr
  (X : HLevel 3)
  : Terminal (path_category X) → iscontr X.
Proof.
  intro T.
  exists (T : path_category X).
  intro x.
  exact (TerminalArrow T x).
Qed.
```

### Adjunctions
Adjunctions are defined in [CategoryTheory.Adjunctions.Core](../../../UniMath/CategoryTheory/Adjunctions/Core.v). The primary definitions are as follows. Note that there are multiple ways to package the same information, which can be a bit confusing:

```coq
adjunction A B                              := ∑ (X : adjunction_data A B), form_adjunction' X
adjunction_data A B                         := ∑ (F : A ⟶ B)
                                                  (G : B ⟶ A),
                                                  functor_identity A ⟹ F ∙ G ×
                                                  G ∙ F ⟹ functor_identity B
form_adjunction'                            := triangle_1_statement X ×
                                                triangle_2_statement X
triangle_1_statement A B (F ,, G ,, μ ,, ɛ) := ∏ a, # F (η a) · ε (F a) = identity (F a)
triangle_2_statement A B (F ,, G ,, μ ,, ɛ) := ∏ b, η (G b) · # G (ε b) = identity (G b)

is_left_adjoint A B F                       := ∑ G, are_adjoints F G
is_right_adjoint A B F                      := ∑ F, are_adjoints F G
are_adjoints A B F G                        := ∑ μɛ, form_adjunction F G (pr1 μɛ) (pr2 μɛ)
form_adjunction A B F G f g                 := form_adjunction' (F ,, G ,, μ ,, ɛ)
```

There are coercions
```coq
is_left_adjoint >-> adjunction_data
adjunction >-> adjunction_data
adjunction >-> are_adjoints
are_adjoints >-> is_left_adjoint
are_adjoints >-> is_right_adjoint
```
and definitions
```coq
(left|right)_adjoint_to_adjunction  : is_(left|right)_adjoint F → adjunction A B
```

Since there are multiple ways to package the same information, there are multiple accessors for the same property on different objects. Here are the accessors for the left and right adjoints, the (co)units and the triangle statements:
```coq
(left|right)_functor                (X : adjunction_data A B)
(left|right)_adjoint                (H : is_(right|left)_adjoint G)

adj(co)unit                         (X : adjunction_data A B)
(co)unit_from_(left|right)_adjoint  (H : is_(left|right)_adjoint F)
(co)unit_from_are_adjoints          (H : are_adjoints F G)

triangle_id_(left|right)_ad         (H : are_adjoints F G)
```
<!-- triangle_(1|2)_statement_from_adjunction  (adj : adjunction A B) -->

One "easy" way to show that a functor is an adjunction is using '(co)reflections' or 'universal arrows'. Having a left adjoint to a functor `F : C ⟶ D` is equivalent to having, for every `d : D`, a 'reflection' of `d` along `F`: an object `c : C` and an arrow `f : D⟦d, F c⟧` such that any other such pair `(c', f')` factors uniquely as `f' = f · #F g` for some `g : C⟦c, c'⟧`. Dually, having a right adjoint is equivalent to having coreflections. This construction is formalized as `(left|right)_adjoint_weq_(co)reflections`.

Some `H : are_adjoints F G` gives an equivalence on homsets `adjunction_hom_weq H X Y : F X --> Y ≃ X --> G Y`, with the map given by `φ_adj H` and the inverse by `φ_adj_inv H`. Conversely, you can show `are_adjoints F G` from a natural equivalence on homsets using `adj_from_nathomweq`. Actually, these mappings between adjunctions and homset equivalences form an equivalence themselves (`adjunction_homsetiso_weq : are_adjoints F G ≃ natural_hom_weq F G`).

### Equivalences

Equivalences, in particular adjoint equivalences, between categories are covered in [CategoryTheory.Equivalences](../../../UniMath/CategoryTheory/Equivalences/) and in particular, in [CategoryTheory.Equivalences.Core](../../../UniMath/CategoryTheory/Equivalences/Core.v).

The primary definitions are
```coq
adj_equiv A B             := ∑ (F : functor A B), adj_equivalence_of_cats F.
adj_equivalence_of_cats F := ∑ (H : is_left_adjoint F), forms_equivalence H.
forms_equivalence X       := ∏ a, is_z_isomorphism (adjunit X a) ×
                              ∏ b, is_z_isomorphism (adjcounit X b).
equivalence_of_cats A B   := ∑ (X : adjunction_data A B), forms_equivalence X.
```

It contains the following coercions
```coq
adj_equiv >-> functor A B
adj_equiv >-> adjunction
adj_equiv >-> adj_equivalence_of_cats
adj_equiv >-> equivalence_of_cats
adj_equivalence_of_cats >-> is_left_adjoint
equivalence_of_cats >-> adjunction_data
```

For the isomorphisms, there are the following accessors:
```coq
adj(co)unitiso                                  (X : equivalence_of_cats A B)
(co)unit_pointwise_z_iso_from_adj_equivalence   (HF : adj_equivalence_of_cats F)
(co)unit_nat_z_iso_from_adj_equivalence_of_cats (HF : adj_equivalence_of_cats F)
(co)unit_z_iso_from_adj_equivalence_of_cats     (HF : adj_equivalence_of_cats F)
```

The file [Equivalences.Core](../../../UniMath/CategoryTheory/Equivalences/Core.v) contains a couple of lemmas and definitions for working with equivalences. First of all, besides the expected constructors, there is also a constructor `make_adj_equivalence_of_cats'` for constructing an adjoint equivalence between `A` and `B` from an adjunction between `B` and `A`. Also, there is a very important lemma `rad_equivalence_of_cats'`, which constructs an adjoint equivalence from a fully faithful and split essentially surjective functor, and a corollary `rad_equivalence_of_cats` which does the same, but for a fully faithful and essentially surjective functor originating from a univalent category.

Then there is a lemma `triangle_2_from_1`, showing that if the unit and counit are isomorphisms, it suffices to show just one of the triangle statements. Also, if we have just an equivalence, `adjointification` constructs an adjoint equivalence from this.

The lemma `weq_on_objects_from_adj_equiv_of_cats` shows that an adjoint equivalence between two univalent categories gives a weak equivalence between the object types.

The file [Equivalences.CompositesAndInverses](../../../UniMath/CategoryTheory/Equivalences/CompositesAndInverses.v) contains the construction of the composite and inverse adjoint equivalences, as well as two lemmas, showing that if two out of three of `F`, `G` and `F ∙ G` are equivalences, the third is an equivalence too:

```coq
comp_adj_equiv                : adj_equiv A B
                                  → adj_equiv B C
                                  → adj_equiv A C
adj_equiv_inv                 : adj_equiv A B
                                  → adj_equiv B A
two_out_of_three_first F G H  : nat_z_iso (F ∙ G) H
                                  → adj_equivalence_of_cats G
                                  → adj_equivalence_of_cats H
                                  → adj_equivalence_of_cats F
two_out_of_three_second F G H : nat_z_iso (F ∙ G) H
                                  → adj_equivalence_of_cats F
                                  → adj_equivalence_of_cats H
                                  → adj_equivalence_of_cats G
```

Lastly, the file [Equivalences.FullyFaithful](../../../UniMath/CategoryTheory/Equivalences/FullyFaithful.v) shows that if a functor is an equivalence, it is both fully faithful (`fully_faithful_from_equivalence`) and essentially surjective (`functor_from_equivalence_is_essentially_surjective`).

## Displayed Categories

In category, many categories are constructed on top of another, often on top of `HSET`. For example, a topological space is "a set with a distinguished set of subsets", a group is "a set with an addition operation" and a ring is "an abelian group that also has a multiplication operation". One way to state this formally is that there are forgetful functors `Top ⟶ HSET` and `Ring ⟶ Group ⟶ HSET`. However, there is another way to frame this, which is as a "displayed category". A displayed category `D` over a category `C`, gives a type of "displayed objects" `D x` (for example, the group structures for a set) for every `x : C`, and a type of displayed morphisms `xx -->[f] yy` for every `f : C⟦x, y⟧`, `xx : D x` and `yy : D y`. Of course, it also has a notion of composition `ff ;; gg`, identity `id_disp` and suitable axioms (like `id_left_disp`, `assoc_disp` and `homsets_disp`).

Displayed categories are a very useful tool in formalization, and sometimes (like when working with a fibration) they actually are a better formalism than forgetful functors. For a theoretical introduction to displayed categories, see [Ahrens & Lumsdaine](https://arxiv.org/abs/1705.04296).

The material about displayed categories is in the [CategoryTheory.DisplayedCats](../../../UniMath/CategoryTheory/DisplayedCats/) directory. The definition of `disp_cat` is in [CategoryTheory.DisplayedCats.Core](../../../UniMath/CategoryTheory/DisplayedCats/Core.v), and its structure is as follows, very much like the structure of `category`:
```coq
disp_cat
  disp_cat_data
    disp_cat_ob_mor
      ob_disp
      mod_disp
    disp_cat_id_comp
      id_disp
      comp_disp
  disp_cat_axioms
    id_left_disp
    id_right_disp
    assoc_disp
    homsets_disp
```

The main datatypes here are defined as follows. Note that, for example, `identity x · f` is not definitionally equal to `f`, so `xx -->[identity x · f] yy` is not the same as `xx -->[f] yy` and we need to transport over `id_left` to get from one to the other:
```coq
disp_cat_ob_mor C     := ∑ (obd : C → UU),                      ∏ x y, obd x → obd y → (x --> y) → UU.
disp_cat_id_comp C D  := ∏ x xx,                                xx -->[identity x] xx ×
                          ∏ x y z f g xx yy zz,                 (xx -->[f] yy) -> (yy -->[g] zz) -> (xx -->[f · g] zz)
disp_cat_axioms C D   := ∏ x y f xx yy ff,                      id_disp _ ;; ff = transportb _ (id_left _) ff ×
                          ∏ x y f xx yy ff,                     ff ;; id_disp _ = transportb _ (id_right _) ff ×
                          ∏ x y z w f g h xx yy zz ww ff gg hh, ff ;; (gg ;; hh) = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh) ×
                          ∏ x y f xx yy,                        isaset (xx -->[f] yy)
```
There are also notions of `z_iso_disp`, `disp_functor`, `disp_nat_trans`, `disp_adjunction`, `equiv_over` etc.

### Some constructions
Here are some constructions that you may use or encounter sometimes:
* For many displayed categories, the additional structure of the morphisms is a mere proposition. For example, for groups, the additional structure of the morphisms is the statement that the function between the sets preserves the group structure. For topological spaces, it is the statement that the function preserves the opens. If this is the case, the axioms about the morphisms follow automatically, and you can use `disp_struct`, defined in [DisplayedCats.Constructions.CategoryWithStructure](../../../UniMath/CategoryTheory/DisplayedCats/Constructions/CategoryWithStructure.v).
* If we have a displayed category `D` over `C` (for example, giving every object of `HSET` a group structure), we can combine the two into the "total category" (for example, the category of groups) `total_category D`, defined in [DisplayedCats.Total](../../../UniMath/CategoryTheory/DisplayedCats/Total.v). It has a forgetful functor `pr1_category : C D, total_category D ⟶ C`.
* Actually, if we just consider `D x` for one `x : C`, we also get a category: `fiber_category D x`, which is denoted `D[{x}]` and defined in [DisplayedCats.Fiber](../../../UniMath/CategoryTheory/DisplayedCats/Fiber.v). Because every morphism in `D[{x}]` is a displayed morphism over `identity x`, composing two of them gives a displayed morphism over `identity x · identity x`. Therefore, morphism composition in this category uses transport over `id_right x` to land in `xx -->[identity x] xx` again.
* If we have displayed categories `D` over `C` and `E` over `total_category D`, we can combine them to get a displayed category `sigma_disp_cat` over `C`, defined in [DisplayedCats.Examples.Sigma](../../../UniMath/CategoryTheory/DisplayedCats/Examples/Sigma.v).
* We can view the product of two categories `C1` and `C2` as a displayed category `disp_cartesian' C1 C2` over `C1`, defined in [DisplayedCats.Examples.Cartesian](../../../UniMath/CategoryTheory/DisplayedCats/Examples/Cartesian.v). Note that the file also contains a definition `disp_cartesian C1 C2`, which uses more of the existing abstract machinery to get the same result. However, this machinery means that composition in this category uses an additional transport, which makes working with it more complicated.
* For displayed categories `D1` and `D2` over `C`, you can combine their added structure into a displayed category `D1 × D2` over `C` (defined in [DisplayedCats.Constructions.Product](../../../UniMath/CategoryTheory/DisplayedCats/Constructions/Product.v)).

### Univalence
One of the advantages of displayed categories is in showing that some category is univalent. This is because distributed over different files, there are lemmas like the following:
```coq
is_univalent_total_category                   : is_univalent C → is_univalent_disp D → is_univalent (total_category D)
is_univalent_disp_iff_fibers_are_univalent D  : is_univalent_disp D <-> (∏ x, is_univalent D[{x}])
is_univalent_sigma_disp E                     : is_univalent_disp D → is_univalent_disp E → is_univalent_disp (sigma_disp_cat E)
is_univalent_disp_cartesian' C1 C2            : is_univalent C2 → is_univalent_disp (disp_cartesian' C1 C2)
dirprod_disp_cat_is_univalent D1 D2           : is_univalent_disp D1 → is_univalent_disp D2 → is_univalent_disp (D1 × D2)
```

### Limits
For showing that a category has limits, there is a similar, though slightly more cumbersome approach: you first show that a displayed category `D` over `C` "creates" a certain limit (`creates_limit`, defined in [DisplayedCats.Limits](../../../UniMath/CategoryTheory/DisplayedCats/Limits.v)), i.e. the limit can be lifted from `C` to `total_category D`. Then you use lemmas like `total_limit`, `creates_limits_sigma_disp_cat` and maybe even `fiber_limit` to show for the desired category that it has limits.

## Bicategories

Bicategories are a 2-dimensional version of categories. They have objects, 1-cells (between objects), and 2-cells (between 1-cells). Associativity and unitality only hold weakly: they do not necessarily hold as identities on 1-cells, but instead they are only guaranteed to hold up to an invertible 2-cell. The key example of a bicategory is the bicategory of categories, whose objects are categories, 1-cells are functors, and 2-cells are natural transformations.

The accessors for bicategories are as follows:
- `x --> y`: type of 1-cells from `x` to `y`. Note: one can also write `B ⟦ x , y ⟧`.
- `f ==> g`: type of 2-cells from `f` to `g`
- `identity x`: identity 1-cell on `x`
- `f · g`: composition of 1-cells
- `id2 f`: identity 2-cell on `f`
- `τ • τ': composition of 2-cells (note that \bu is used to type •)
- `lunitor f`: left unitor (`identity _ · f ==> f`)
- `linvunitor f`: inverse of the left unitor (`f ==> identity _ · f`)
- `runitor f`: right unitor (`f · identity _ ==> f`)
- `rinvunitor f`: inverse of the right unitor (`f ==> f · identity _`)
- `lassociator f g h`: left associator (`f · (g · h) ==> (f · g) · h`)
- `rassociator f g h`: right associator (`(f · g) · h ==> f · (g · h)`)
- `f ◃ τ`: left whiskering. Given `f : x --> y` and `τ : g₁ ==> g₂` where `g₁ g₂ : y --> z`, then `f ◃ τ : f · g₁ ==> f · g₂`
- `τ ▹ g`: right whiskering. Given `g : y --> z` and `τ : f₁ ==> f₂` where `f₁ f₂ : x --> y`, then `τ ▹ g : f₁ · g ==> f₂ · g`

There are various laws, which can be found in `Core/Bicat.v` and `Core/Bicategory_laws.v`.

### Invertible 2-cells and adjoint equivalences

An invertible 2-cell `τ` from 1-cells `f` to `g` is given by 2-cells `τ : f ==> g` and `τ^-1 : g ==> f` that compose to the identity. The type expressing that some 2-cell `τ : f ==> g` is invertible, is a proposition. The type of invertible 2-cells is denoted by `invertible_2cell f g`.

An eqivalence `f` from `x` to `y` consists of 1-cells `f : x --> y` and `g : y --> x` together with invertible 2-cells witnessing that both `f · g` and `g · f` are isomorphic to the identity. Note that we do not require any coherences. The type of equivalences from `x` to `y` is denoted by `left_equivalence x y`.

Finally, an adjoint equivalence `f` from `x` to `y` is given by an equivalence that satisfies the triangle equality for the unit and counit. The type of adjoint equivalences from `x` to `y` is denoted by `adjoint_equivalence x y`, and the type expressing that `f` is an adjoint equivalence is denoted by `left_adjoint_equivalence f`. The important statements about adjoint equivalences are:
- `equiv_to_adjequiv`: refines a (not necessarily coherent) equivalence into an adjoint equivalence
- `isaprop_left_adjoint_equivalence`: the type expressing that a 1-cell is an adjoint equivalence, is a proposition if the bicategory is locally univalent

Invertible 2-cells and adjoint equivalences are used to define local and global univalence of bicategories. A bicategory is locally univalent (`is_univalent_2_1`) if identity of 1-cells corresponds to invertible 2-cells and a bicategory is globally univalent (`is_univalent_2_0`) if identity of objects corresponds to adjoint equivalences. A bicategory is univalent if it is both locally and globally univalent.

### Displayed bicategories

Displayed bicategories are a useful tool for modularly constructing bicategories, and to conveniently prove that the resulting bicategories are univalent. The ideas behind displayed bicategories is the same as for displayed categories. The only difference is that displayed bicategories are 2-dimensional in nature meaning that they come with a notion of displayed 2-cell. In UniMath, we have the basic theory of displayed bicategories, and a wide variety of displayed bicategories. The theory includes statements to prove the univalence of the total bicategory. In addition, there is a formalization of the notion of fibration of bicategories (`cleaving_of_bicats`).

Relevant identifiers:
- `disp_bicat`: the type of displayed bicategories
- `disp_univalent_2_0`: global univalence for displayed bicategories
- `disp_univalent_2_1`: local univalence for displayed bicategories
- `disp_univalent_2`: univalence for displayed bicategories
- `total_bicat`: the total bicategory
- `pr1_psfunctor`: the projection
- `total_is_univalent_2_1`: local univalence of the total bicategory
- `total_is_univalent_2_0`: global univalence of the total bicategory

The bicategory of pseudofunctors is defined using displayed bicategories. The reason behind this is that it simplifies the proof of univalence. The bicategory of pseudofunctors is denoted by `psfunctor_bicat B₁ B₂`, the type of pseudofunctors from `B₁` to `B₂` is denoted by `psfunctor B₁ B₂`, the type of pseudotransformations from `F` to `G` is denoted by `pstrans F G`, and the type of modifications from `τ₁` to `τ₂` is denoted by `modification τ₁ τ₂`. Finally, the type of invertible modifications is denoted by `invertible_modification τ₁ τ₂`.

### References
- ``Bicategories in univalent foundations'' by Ahrens, Frumin, Maggesi, Veltri, Van der Weide.
- ``Bicategorical type theory: semantics and syntax'' by Ahrens, North, Van der Weide.
- ``The Formal Theory of Monads, Univalently'' by Van der Weide.
- ``Univalent Double Categories'' by Van der Weide, Rasekh, Ahrens, North.
- ``Insights from univalent foundations: A case study using double categories'' by Rasekh, Van der Weide, Ahrens North.
- ``The internal languages of univalent categories'' by Van der Weide
