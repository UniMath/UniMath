(**********************************************************************

 Enriched slice categories

 In this file, we define enriched slice categories. The approach that
 we take, is based on the fact that slice categories can be defined
 using dialgebras. As such, we can reuse the fact that we already
 showed that the category of dialgebras has an enrichment, and we can
 specialize that to obtain an enrichment for slice categories.

 Let's be more specific. Suppose that we have a category `C` and an
 object `x` in `C`. To construct the slice category `C/x` we take the
 category of dialgebras between the identity and the functor that is
 constantly `x`. As such, the objects of this category are pairs of an
 object `a` in `C` together with a morphism `a --> x`. As such, this
 corresponds to objects in the slice category `C/x`. The same can be
 said for morphisms.

 Note that we assume that the monoidal category `V` has equalizers and
 that the unit is terminal. The reason for that, is because of how
 morphisms in the slice category are defined. If we have two objects
 `f : a --> x` and `g : b --> x` in the slice `C/x`, then a morphism
 from `f` to `g` consists of a morphism `h : a --> b` such that we have
 `f = g · h`. Equalizers are used to o encode the commutativity
 requirement. If one were to define it concretely, one would take the
 equalizer of the following diagram
 ```
               h ↦ h · g
             ------------>
    a --> b                a --> x
             ----> 𝟙 ---->
                      f
 ```
 Instead of this concrete definition, we reuse that we already defined
 the enriched category of dialgebras.

 Contents
 1. Enrichment for slice categories
 2. An equivalence between dialgebras and the slice

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Categories.Dialgebras.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.DialgebraEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedSlice.
  Context (V : monoidal_cat)
          (HV𝟙 : isTerminal V (I_{V}))
          (HV : Equalizers V)
          {C : category}
          (E : enrichment C V)
          (x : C).

  (**
   1. Enrichment for slice categories
   *)
  Definition slice_cat_enrichment
    : enrichment
        (dialgebra (functor_identity C) (constant_functor C C x))
        V
    := dialgebra_enrichment
         V HV
         (functor_id_enrichment E)
         (functor_constant_enrichment HV𝟙 x E E).

  (**
   2. An equivalence between dialgebras and the slice
   *)
  Definition dialgebra_to_slice_data
    : functor_data
        (dialgebra (functor_identity C) (constant_functor C C x))
        (slice_cat C x).
  Proof.
    use make_functor_data.
    - exact (λ x, x).
    - refine (λ x y f, pr1 f ,, _) ; cbn.
      abstract
        (exact (!(id_right _) @ pr2 f)).
  Defined.

  Definition dialgebra_to_slice_is_functor
    : is_functor dialgebra_to_slice_data.
  Proof.
    repeat split.
    - intro ; intros.
      use subtypePath ; [ intro ; apply homset_property | ] ; cbn.
      apply idpath.
    - intro ; intros.
      use subtypePath ; [ intro ; apply homset_property | ] ; cbn.
      apply idpath.
  Qed.

  Definition dialgebra_to_slice
    : dialgebra (functor_identity C) (constant_functor C C x) ⟶ slice_cat C x.
  Proof.
    use make_functor.
    - exact dialgebra_to_slice_data.
    - exact dialgebra_to_slice_is_functor.
  Defined.

  Definition slice_to_dialgebra_data
    : functor_data
        (slice_cat C x)
        (dialgebra (functor_identity C) (constant_functor C C x)).
  Proof.
    use make_functor_data.
    - exact (λ x, x).
    - refine (λ x y f, pr1 f ,, _) ; cbn.
      abstract
        (exact (id_right _ @ pr2 f)).
  Defined.

  Definition slice_to_dialgebra_is_functor
    : is_functor slice_to_dialgebra_data.
  Proof.
    repeat split.
    - intro ; intros.
      use subtypePath ; [ intro ; apply homset_property | ] ; cbn.
      apply idpath.
    - intro ; intros.
      use subtypePath ; [ intro ; apply homset_property | ] ; cbn.
      apply idpath.
  Qed.

  Definition slice_to_dialgebra
    : slice_cat C x ⟶ dialgebra (functor_identity C) (constant_functor C C x).
  Proof.
    use make_functor.
    - exact slice_to_dialgebra_data.
    - exact slice_to_dialgebra_is_functor.
  Defined.

  Definition dialgebra_to_slice_unit
    : functor_identity _ ⟹ dialgebra_to_slice ∙ slice_to_dialgebra.
  Proof.
    use make_nat_trans.
    - refine (λ f, identity _ ,, _).
      abstract
        (cbn ;
         exact (id_right _ @ !(id_left _))).
    - abstract
        (intros f₁ f₂ τ ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
         exact (id_right _ @ !(id_left _))).
  Defined.

  Definition dialgebra_to_slice_counit
    : slice_to_dialgebra ∙ dialgebra_to_slice ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - refine (λ f, identity _ ,, _).
      abstract
        (cbn ;
         exact (!(id_left _))).
    - abstract
        (intros f₁ f₂ τ ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
         exact (id_right _ @ !(id_left _))).
  Defined.

  Definition dialgebra_to_slice_adj_equiv
    : adj_equivalence_of_cats dialgebra_to_slice.
  Proof.
    simple refine ((_ ,, ((_ ,, _) ,, _ ,, _)) ,, _ ,, _).
    - exact slice_to_dialgebra.
    - exact dialgebra_to_slice_unit.
    - exact dialgebra_to_slice_counit.
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
         apply id_left).
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
         apply id_left).
    - intro f.
      use is_z_iso_dialgebra.
      cbn.
      apply is_z_isomorphism_identity.
    - intro f.
      use z_iso_to_slice_precat_z_iso.
      cbn.
      apply is_z_isomorphism_identity.
  Defined.
End EnrichedSlice.
