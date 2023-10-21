(**********************************************************************

 Image factorization of enriched categories

 Enriched functors between enriched categories can be factorized into
 a essentially surjective functor followed by a enriched fully faithful
 functor.

 Contents
 1. The enriched image
 2. The factorization functors
 3. The commutation

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section ImageEnriched.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {F : C₁ ⟶ C₂}
          (EF : functor_enrichment F E₁ E₂).

  (**
   1. The enriched image
   *)
  Definition image_enrichment
    : enrichment (full_img_sub_precategory F) V
    := fullsub_enrichment V E₂ _.

  (**
   2. The factorization functors
   *)
  Definition image_incl_enrichment
    : functor_enrichment
        (sub_precategory_inclusion _ _)
        image_enrichment
        E₂
    := fullsub_inclusion_enrichment V E₂ _.

  Definition image_incl_enrichment_fully_faithful
    : fully_faithful_enriched_functor
        image_incl_enrichment
    := fullsub_inclusion_enrichment_fully_faithful V E₂ _.

  Definition image_proj_enrichment
    : functor_enrichment
        (functor_full_img _)
        E₁
        image_enrichment.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (λ x y, EF x y).
    - abstract
        (intro x ; cbn ;
         exact (functor_enrichment_id EF x)).
    - abstract
        (intros x y z ; cbn ;
         exact (functor_enrichment_comp EF x y z)).
    - abstract
        (intros x y f ;
         exact (functor_enrichment_from_arr EF f)).
  Defined.

  (**
   3. The commutation
   *)
  Definition image_factorization_enriched_commutes
    : nat_trans_enrichment
        (full_image_inclusion_commute_nat_iso F)
        (functor_comp_enrichment
           image_proj_enrichment
           image_incl_enrichment)
        EF.
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite precomp_arr_id, postcomp_arr_id.
    rewrite !id_right.
    apply idpath.
  Qed.

  Definition image_factorization_enriched_commutes_inv
    : nat_trans_enrichment
        (nat_z_iso_inv (full_image_inclusion_commute_nat_iso F))
        EF
        (functor_comp_enrichment
           image_proj_enrichment
           image_incl_enrichment).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite precomp_arr_id, postcomp_arr_id.
    rewrite !id_right.
    apply idpath.
  Qed.
End ImageEnriched.

Arguments image_enrichment {V C₁ C₂} E₂ F.
Arguments image_incl_enrichment {V C₁ C₂} E₂ F.
