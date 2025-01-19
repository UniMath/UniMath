(**********************************************************************

 The full subcategory of enriched category

 We show that the full subcategory of an enriched category is again
 enriched over the same monoidal category. We also show that the
 inclusion is an enriched functor.

 Contents
 1. The enrichment over the full subcategory
 2. The enrichment of the inclusion

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
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Section FullSub.
  Context (V : monoidal_cat)
          {C : category}
          (E : enrichment C V)
          (P : C → hProp).

  (**
   1. The enrichment over the full subcategory
   *)
  Definition fullsub_enrichment_data
    : enrichment_data
        (subcategory C (full_sub_precategory P))
        V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, E ⦃ pr1 x , pr1 y ⦄).
    - exact (λ x, enriched_id E (pr1 x)).
    - exact (λ x y z, enriched_comp E (pr1 x) (pr1 y) (pr1 z)).
    - exact (λ x y f, enriched_from_arr E (pr1 f)).
    - exact (λ x y f, enriched_to_arr E f ,, tt).
  Defined.

  Definition fullsub_enrichment_laws
    : enrichment_laws fullsub_enrichment_data.
  Proof.
    repeat split ; intros ; cbn.
    - apply enrichment_id_left.
    - apply enrichment_id_right.
    - apply enrichment_assoc.
    - use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      apply enriched_to_from_arr.
    - apply enriched_from_to_arr.
    - use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      apply enriched_to_arr_id.
    - use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      apply enriched_to_arr_comp.
  Qed.

  Definition fullsub_enrichment
    : enrichment
        (subcategory C (full_sub_precategory P))
        V.
  Proof.
    simple refine (_ ,, _).
    - exact fullsub_enrichment_data.
    - exact fullsub_enrichment_laws.
  Defined.

  Proposition fullsub_enrichment_precomp_arr
              {x y : subcategory C (full_sub_precategory P)}
              (w : subcategory C (full_sub_precategory P))
              (f : x --> y)
    : precomp_arr fullsub_enrichment w f
      =
      precomp_arr E (pr1 w) (pr1 f).
  Proof.
    apply idpath.
  Qed.

  Proposition fullsub_enrichment_postcomp_arr
              {x y : subcategory C (full_sub_precategory P)}
              (w : subcategory C (full_sub_precategory P))
              (f : x --> y)
    : postcomp_arr fullsub_enrichment w f
      =
      postcomp_arr E (pr1 w) (pr1 f).
  Proof.
    apply idpath.
  Qed.

  (**
   2. The enrichment of the inclusion
   *)
  Definition fullsub_inclusion_enrichment
    : functor_enrichment
        (sub_precategory_inclusion _ _)
        fullsub_enrichment
        E.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, identity _).
    - repeat split.
      + abstract
          (cbn ; intro x ;
           apply id_right).
      + abstract
          (cbn ; intros x y z ;
           rewrite id_right ;
           rewrite tensor_id_id ;
           rewrite id_left ;
           apply idpath).
      + abstract
          (cbn ; intros x y f ;
           rewrite id_right ;
           apply idpath).
  Defined.

  Definition fullsub_inclusion_enrichment_fully_faithful
    : fully_faithful_enriched_functor
        fullsub_inclusion_enrichment.
  Proof.
    intros x y.
    apply is_z_isomorphism_identity.
  Defined.
End FullSub.
