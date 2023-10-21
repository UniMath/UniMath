(**********************************************************************

 The enriched Kleisli category

 In this file we define an enrichment of the Kleisli category (that is
 not guaranteed to be univalent).

 Contents
 1. Data of the enrichment
 2. The laws of the enrichment
 3. The enrichment

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedKleisli.
  Context {V : monoidal_cat}
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  (**
   1. Data of the enrichment
   *)
  Definition Kleisli_cat_monad_enrichment_data
    : enrichment_data (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, E ⦃ x , M y ⦄).
    - exact (λ x, enriched_from_arr E (η M x)).
    - exact (λ x y z,
             endo_of_monad_enrichment EM y (M z) #⊗ identity _
             · enriched_comp E x (M y) (M(M z))
             · postcomp_arr E x (μ M z)).
    - exact (λ x y f, enriched_from_arr E (f · η M y)).
    - exact (λ x y f, enriched_to_arr E f).
  Defined.

  (**
   2. The laws of the enrichment
   *)
  Definition Kleisli_cat_monad_enrichment_laws
    : enrichment_laws Kleisli_cat_monad_enrichment_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite enriched_comp_postcomp_arr.
        rewrite !assoc.
        rewrite <- !tensor_comp_id_r.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (@Monad_law2 _ M y).
        }
        rewrite enriched_from_arr_id.
        rewrite <- enrichment_id_left.
        apply idpath.
      }
      apply idpath.
    - intros x y ; cbn.
      rewrite <- enriched_id_precomp_arr.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite <- enriched_comp_precomp_arr.
        rewrite !assoc.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_runitor.
      refine (_ @ id_right _).
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite (nat_trans_enrichment_to_comp (unit_of_monad_enrichment EM)) ; cbn.
      rewrite id_left.
      rewrite <- postcomp_arr_comp.
      refine (_ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      exact (@Monad_law1 _ M y).
    - intros w x y z ; cbn.
      rewrite !assoc'.
      rewrite !enriched_comp_postcomp_arr.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite functor_enrichment_comp.
        rewrite !assoc'.
        rewrite enriched_comp_postcomp_arr.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite !id_left, !id_right.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite tensor_split'.
        rewrite tensor_comp_id_r.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite !assoc.
        rewrite <- functor_enrichment_postcomp_arr.
        rewrite !assoc'.
        rewrite <- postcomp_arr_comp.
        do 2 apply maponpaths.
        exact (@Monad_law3 _ M z).
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !tensor_comp_id_l.
      rewrite !tensor_comp_id_r.
      rewrite !tensor_comp_id_l.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite <- precomp_postcomp_arr_assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite mon_rassociator_lassociator.
        rewrite id_right.
        apply idpath.
      }
      rewrite <- !tensor_comp_mor.
      rewrite tensor_id_id.
      rewrite !id_left, !id_right.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) y (M z)).
      }
      cbn.
      rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      apply idpath.
    - intros x y f ; cbn.
      etrans.
      {
        do 3 apply maponpaths.
        exact (@bind_η _ M y).
      }
      rewrite id_right.
      apply enriched_to_from_arr.
    - intros x y f ; cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (@bind_η _ M y).
      }
      rewrite id_right.
      apply enriched_from_to_arr.
    - intros x ; cbn.
      apply enriched_to_from_arr.
    - intros x y z f g ; cbn.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          do 3 apply maponpaths.
          exact (@bind_η _ M y).
        }
        rewrite id_right.
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths.
          exact (@bind_η _ M z).
        }
        rewrite id_right.
        apply idpath.
      }
      rewrite enriched_comp_postcomp_arr.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_mor.
        rewrite !id_right.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- enriched_to_arr_comp.
      apply idpath.
  Qed.

  (**
   3. The enrichment
   *)
  Definition Kleisli_cat_monad_enrichment
    : enrichment (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _).
    - exact Kleisli_cat_monad_enrichment_data.
    - exact Kleisli_cat_monad_enrichment_laws.
  Defined.

  Definition Left_Kleisli_functor_enrichment_laws
    : @is_functor_enrichment
        _ _ _
        (Left_Kleisli_functor M)
        E
        Kleisli_cat_monad_enrichment
        (λ x y : C, postcomp_arr E x (η M y)).
  Proof.
    repeat split.
    - intro x.
      exact (enriched_id_postcomp_arr E (η M x)).
    - intros x y z ; cbn.
      rewrite !assoc'.
      rewrite !enriched_comp_postcomp_arr.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_r.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        rewrite <- precomp_postcomp_arr_assoc.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      apply maponpaths_2.
      rewrite !assoc.
      rewrite <- functor_enrichment_postcomp_arr.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- postcomp_arr_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply Monad_law2.
        }
        rewrite postcomp_arr_id.
        apply id_left.
      }
      rewrite (nat_trans_enrichment_to_comp (unit_of_monad_enrichment EM)).
      apply id_left.
    - intros x y f ; cbn.
      rewrite enriched_from_arr_postcomp.
      apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      apply bind_η.
  Qed.

  Definition Left_Kleisli_functor_enrichment
    : functor_enrichment
        (Left_Kleisli_functor M)
        E
        Kleisli_cat_monad_enrichment.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, postcomp_arr E x (η M y)).
    - exact Left_Kleisli_functor_enrichment_laws.
  Defined.
End EnrichedKleisli.
