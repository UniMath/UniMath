(*****************************************************************

 Enrichment over the category of sets

 One of the simplest categories over which we can study enrichments
 is the category of sets. In this file, we show that enrichments
 over the category of sets exist and that they are unique. From
 that, we conclude that the notions of category, functor, and
 natural transformations are equivalent to their enrichment
 counterpart if we look at enrichments over the category of sets.

 Contents
 1. Enrichments over sets are unique for categories
 2. Enrichments over sets are unique for functors
 3. Enrichments over sets are unique for natural transformations

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SetCartesianMonoidal.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

(**
 1. Enrichments over sets are unique for categories
 *)
Section UniqueSetEnrichment.
  Context (C : category).

  Definition set_enrichment_data
    : enrichment_data C SET_monoidal_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, make_hSet (x --> y) (homset_property C x y)).
    - exact (λ x _, identity x).
    - exact (λ x y z fg, pr2 fg · pr1 fg).
    - exact (λ x y f _, f).
    - exact (λ x y f, f tt).
  Defined.

  Proposition set_enrichment_laws
    : enrichment_laws set_enrichment_data.
  Proof.
    repeat split.
    - intros x y.
      use funextsec ; intro ; cbn.
      rewrite id_right.
      apply idpath.
    - intros x y.
      use funextsec ; intro ; cbn.
      rewrite id_left.
      apply idpath.
    - intros w x y z.
      use funextsec ; intro ; cbn.
      apply assoc.
    - intros x y f.
      use funextsec ; intro w ; cbn.
      apply maponpaths.
      apply isapropunit.
  Qed.

  Definition set_enrichment
    : enrichment C SET_monoidal_cat.
  Proof.
    simple refine (_ ,, _).
    - exact set_enrichment_data.
    - exact set_enrichment_laws.
  Defined.

  Theorem iscontr_set_enrichment
    : iscontr (enrichment C SET_monoidal_cat).
  Proof.
    refine (set_enrichment ,, _).
    intro E.
    use subtypePath.
    {
      intro.
      apply isaprop_enrichment_laws.
    }
    use (invweq (total2_paths_equiv _ _ _)).
    use (invmap (enrichment_data_hom_path _ (pr1 E) set_enrichment_data)).
    {
      exact is_univalent_HSET.
    }
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - intros x y.
      use make_z_iso.
      + exact (λ f, enriched_to_arr E (λ _, f)).
      + exact (λ f, enriched_from_arr E f tt).
      + split.
        * use funextsec ; intro f ; cbn.
          rewrite enriched_from_to_arr.
          apply idpath.
        * use funextsec ; intro f ; cbn.
          refine (_ @ enriched_to_from_arr E _).
          apply maponpaths.
          use funextsec.
          intro z.
          apply maponpaths.
          apply isapropunit.
    - intro x ; use funextsec ; intro f ; cbn.
      refine (_ @ enriched_to_arr_id E _).
      apply maponpaths.
      use funextsec.
      intro z.
      apply maponpaths.
      apply isapropunit.
    - intros x y z ; use funextsec ; intro f ; cbn.
      use (invmaponpathsweq (invweq (_ ,, isweq_enriched_to_arr E _ _))) ; cbn.
      rewrite enriched_from_arr_comp ; cbn.
      rewrite !enriched_from_to_arr.
      apply idpath.
    - intros x y f ; use funextsec ; intro w ; cbn.
      refine (_ @ enriched_to_from_arr E _).
      apply maponpaths.
      use funextsec.
      intro z.
      apply maponpaths.
      apply isapropunit.
    - intros x y f ; cbn.
      apply maponpaths.
      use funextsec.
      intro z.
      apply maponpaths.
      apply isapropunit.
  Qed.
End UniqueSetEnrichment.

Definition cat_with_set_enrichment_weq_cat
  : cat_with_enrichment SET_monoidal_cat ≃ category.
Proof.
  use weqpr1.
  intro.
  apply iscontr_set_enrichment.
Defined.

(**
 2. Enrichments over sets are unique for functors
 *)
Section UniqueFunctorSetEnrichment.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition functor_set_enrichment
    : functor_enrichment
        F
        (set_enrichment C₁)
        (set_enrichment C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, #F f).
    - repeat split.
      + abstract
          (intro x ; cbn ;
           use funextsec ; intro ;
           apply functor_id).
      + abstract
          (intros x y f ; cbn ;
           use funextsec ; intro ;
           apply functor_comp).
  Defined.

  Theorem iscontr_functor_set_enrichment
    : iscontr
        (functor_enrichment
           F
           (set_enrichment C₁)
           (set_enrichment C₂)).
  Proof.
    refine (functor_set_enrichment ,, _).
    intro EF.
    use subtypePath.
    {
      intro.
      apply isaprop_is_functor_enrichment.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    cbn.
    exact (!(eqtohomot (functor_enrichment_from_arr EF f) tt)).
  Qed.
End UniqueFunctorSetEnrichment.

Definition functor_with_set_enrichment_weq_functor
           (C₁ C₂ : category)
  : functor_with_enrichment (C₁ ,, set_enrichment C₁) (C₂ ,, set_enrichment C₂)
    ≃
    C₁ ⟶ C₂.
Proof.
  use weqpr1.
  intro.
  apply iscontr_functor_set_enrichment.
Defined.

(**
 3. Enrichments over sets are unique for natural transformations
 *)
Section UniqueNatTransSetEnrichment.
  Context {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          (τ : F ⟹ G).

  Definition nat_trans_set_enrichment
    : nat_trans_enrichment
        τ
        (functor_set_enrichment F)
        (functor_set_enrichment G).
  Proof.
    intros x y ; cbn.
    use funextsec ; intro f ; cbn.
    exact (!(nat_trans_ax τ _ _ f)).
  Qed.

  Theorem iscontr_nat_trans_set_enrichment
    : iscontr
        (nat_trans_enrichment
           τ
           (functor_set_enrichment F)
           (functor_set_enrichment G)).
  Proof.
    refine (nat_trans_set_enrichment ,, _).
    intro.
    apply isaprop_nat_trans_enrichment.
  Qed.
End UniqueNatTransSetEnrichment.

Definition nat_trans_with_set_enrichment_weq_nat_trans
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : @nat_trans_with_enrichment
      _
      (C₁ ,, set_enrichment C₁)
      (C₂ ,, set_enrichment C₂)
      (F ,, functor_set_enrichment F)
      (G ,, functor_set_enrichment G)
    ≃
    F ⟹ G.
Proof.
  use weq_iso.
  - exact (λ τ, pr1 τ ,, is_nat_trans_from_enrichment (pr2 τ)).
  - exact (λ τ, pr1 τ ,, nat_trans_set_enrichment τ).
  - abstract
      (intro τ ;
       use eq_nat_trans_with_enrichment ;
       intro x ; cbn ;
       apply idpath).
  - abstract
      (intro τ ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       apply idpath).
Defined.
