(********************************************************************************************

 Laws for representable profunctors

 In this file, we establish the laws that are necessary to show that representable profunctors
 give companion pairs and conjoints in the double bicategory of enriched profunctors.

 Content
 1. Laws for the left representable
 2. Laws for the right representable

 ********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Laws for the left representable *)
Proposition representable_enriched_profunctor_left_left_eq
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
  : rwhisker_enriched_profunctor_square
      (runitor_enriched_profunctor
         (representable_enriched_profunctor_left EF))
      (lwhisker_enriched_profunctor_square
         (linvunitor_enriched_profunctor
            (representable_enriched_profunctor_left EF))
         (comp_v_enriched_profunctor_square
            (representable_enriched_profunctor_left_counit EF)
            (representable_enriched_profunctor_left_unit EF)))
    =
    id_h_enriched_profunctor_square (representable_enriched_profunctor_left EF).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  unfold linvunitor_enriched_profunctor_mor.
  refine (_ @ mon_linvunitor_lunitor _).
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply (comp_v_enriched_profunctor_square_mor_comm
             (representable_enriched_profunctor_left_counit _)
             (representable_enriched_profunctor_left_unit _)).
  }
  cbn.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    apply (runitor_enriched_profunctor_mor_comm
             (representable_enriched_profunctor_left _)).
  }
  cbn.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite assoc.
    rewrite sym_mon_braiding_inv.
    apply id_left.
  }
  rewrite !assoc.
  rewrite <- tensor_comp_id_r.
  rewrite functor_enrichment_id.
  rewrite enrichment_id_left.
  apply idpath.
Qed.

Proposition representable_enriched_profunctor_left_right_eq
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
  : dwhisker_enriched_profunctor_square
      (rinvunitor_enrichment EF)
      (uwhisker_enriched_profunctor_square
         (lunitor_enrichment EF)
         (comp_h_enriched_profunctor_square
            (representable_enriched_profunctor_left_counit EF)
            (representable_enriched_profunctor_left_unit EF)))
    =
    id_v_enriched_profunctor_square EF.
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite id_right.
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  rewrite !enriched_from_arr_id.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- enrichment_id_left.
    rewrite mon_lunitor_linvunitor.
    rewrite id_left.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite <- enrichment_id_right.
    rewrite sym_mon_braiding_runitor.
    apply idpath.
  }
  apply mon_linvunitor_lunitor.
Qed.

(** * 2. Laws for the right representable *)
Proposition representable_enriched_profunctor_right_left_eq
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
  : lwhisker_enriched_profunctor_square
      (rinvunitor_enriched_profunctor
         (representable_enriched_profunctor_right EF))
      (rwhisker_enriched_profunctor_square
         (lunitor_enriched_profunctor
            (representable_enriched_profunctor_right EF))
         (comp_v_enriched_profunctor_square
            (representable_enriched_profunctor_right_counit EF)
            (representable_enriched_profunctor_right_unit EF)))
    =
    id_h_enriched_profunctor_square (representable_enriched_profunctor_right EF).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  unfold rinvunitor_enriched_profunctor_mor.
  refine (_ @ mon_rinvunitor_runitor _).
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply (comp_v_enriched_profunctor_square_mor_comm
             (representable_enriched_profunctor_right_counit _)
             (representable_enriched_profunctor_right_unit _)).
  }
  cbn.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    apply (lunitor_enriched_profunctor_mor_comm
             (representable_enriched_profunctor_right _)).
  }
  cbn.
  rewrite !assoc.
  rewrite <- tensor_comp_id_l.
  rewrite functor_enrichment_id.
  rewrite enrichment_id_right.
  apply idpath.
Qed.

Proposition representable_enriched_profunctor_right_right_eq
            {V : benabou_cosmos}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {F : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
  : dwhisker_enriched_profunctor_square
      (linvunitor_enrichment EF)
      (uwhisker_enriched_profunctor_square
         (runitor_enrichment EF)
         (comp_h_enriched_profunctor_square
            (representable_enriched_profunctor_right_unit EF)
            (representable_enriched_profunctor_right_counit EF)))
    =
    id_v_enriched_profunctor_square EF.
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  rewrite id_right.
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  rewrite !enriched_from_arr_id.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- enrichment_id_left.
    rewrite mon_lunitor_linvunitor.
    rewrite id_left.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite <- enrichment_id_right.
    rewrite sym_mon_braiding_runitor.
    apply idpath.
  }
  apply mon_linvunitor_lunitor.
Qed.
