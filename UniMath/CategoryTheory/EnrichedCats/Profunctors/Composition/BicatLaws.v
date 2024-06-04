(*****************************************************************************************

 Bicategory laws for enriched profunctors

 In this file we establish the bicategory laws for enriched profunctors.

 Contents
 1. Naturality for the associator
 2. The triangle law
 3. The pentagon law

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Invertible.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Coend.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.CompositionProf.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Unitors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Associators.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.Whiskering.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Naturality for the associator *)
Proposition enriched_lwhisker_lwhisker
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            (P : E₁ ↛e E₂)
            (Q : E₂ ↛e E₃)
            {R₁ R₂ : E₃ ↛e E₄}
            (τ : enriched_profunctor_transformation R₁ R₂)
  : enriched_profunctor_comp_transformation
      (lwhisker_enriched_profunctor P (lwhisker_enriched_profunctor Q τ))
      (lassociator_enriched_profunctor P Q R₂)
    =
    enriched_profunctor_comp_transformation
      (lassociator_enriched_profunctor P Q R₁)
      (lwhisker_enriched_profunctor (comp_enriched_profunctor P Q) τ).
Proof.
  use eq_enriched_profunctor_transformation ; intros z w ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros x.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  use is_inj_internal_transpose.
  use from_comp_enriched_profunctor_eq.
  intros y.
  use internal_funext.
  intros v h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear v h.
  unfold internal_transpose.
  rewrite !internal_beta.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    rewrite !assoc'.
    do 2 apply maponpaths.
    apply (lwhisker_enriched_profunctor_mor_comm
             (comp_enriched_profunctor P Q)).
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    rewrite <- tensor_comp_id_l.
    do 2 apply maponpaths_2.
    apply maponpaths.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply lassociator_enriched_profunctor_data_comm.
  }
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  unfold lassociator_enriched_profunctor_mor_ob.
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    rewrite !assoc'.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite tensor_rassociator.
    apply idpath.
  }
  rewrite !assoc.
  rewrite sym_mon_braiding_inv.
  rewrite id_left.
  rewrite tensor_id_id.
  apply idpath.
Qed.

Proposition enriched_rwhisker_lwhisker
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            (P : E₁ ↛e E₂)
            {Q₁ Q₂ : E₂ ↛e E₃}
            (τ : enriched_profunctor_transformation Q₁ Q₂)
            (R : E₃ ↛e E₄)
  : enriched_profunctor_comp_transformation
      (lwhisker_enriched_profunctor P (rwhisker_enriched_profunctor τ R))
      (lassociator_enriched_profunctor P Q₂ R)
    =
    enriched_profunctor_comp_transformation
      (lassociator_enriched_profunctor P Q₁ R)
      (rwhisker_enriched_profunctor (lwhisker_enriched_profunctor P τ) R).
Proof.
  use eq_enriched_profunctor_transformation ; intros z w ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros x.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply lassociator_enriched_profunctor_data_comm.
  }
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  rewrite !assoc'.
  apply maponpaths.
  use is_inj_internal_lam.
  use from_comp_enriched_profunctor_eq.
  intros y.
  use internal_funext.
  intros v h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear v h.
  rewrite !internal_beta.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply (rwhisker_enriched_profunctor_mor_comm
             (lwhisker_enriched_profunctor P τ)).
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    do 2 apply maponpaths_2.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite <- tensor_comp_id_r.
    do 3 apply maponpaths_2.
    apply rwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  unfold lassociator_enriched_profunctor_mor_ob.
  rewrite tensor_comp_id_r.
  rewrite !assoc.
  do 2 apply maponpaths_2.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  rewrite tensor_rassociator.
  apply idpath.
Qed.

Proposition enriched_rwhisker_rwhisker
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {P₁ P₂ : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P₁ P₂)
            (Q : E₂ ↛e E₃)
            (R : E₃ ↛e E₄)
  : enriched_profunctor_comp_transformation
      (lassociator_enriched_profunctor P₁ Q R)
      (rwhisker_enriched_profunctor (rwhisker_enriched_profunctor τ Q) R)
    =
    enriched_profunctor_comp_transformation
      (rwhisker_enriched_profunctor τ (comp_enriched_profunctor Q R))
      (lassociator_enriched_profunctor P₂ Q R).
Proof.
  use eq_enriched_profunctor_transformation ; intros z w ; cbn.
  use from_comp_enriched_profunctor_eq.
  intros x.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply rwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    apply lassociator_enriched_profunctor_data_comm.
  }
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  use is_inj_internal_lam.
  use from_comp_enriched_profunctor_eq.
  intros y.
  use internal_funext.
  intros v h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear v h.
  rewrite !internal_beta.
  rewrite !assoc.
  etrans.
  {
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite <- tensor_comp_id_r.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  unfold lassociator_enriched_profunctor_mor_ob.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite <- tensor_id_id.
  rewrite tensor_rassociator.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    apply (rwhisker_enriched_profunctor_mor_comm
             (rwhisker_enriched_profunctor τ Q)).
  }
  rewrite !assoc.
  etrans.
  {
    rewrite <- tensor_comp_id_r.
    do 2 apply maponpaths_2.
    apply rwhisker_enriched_profunctor_mor_comm.
  }
  rewrite tensor_comp_id_r.
  apply idpath.
Qed.

(** * 2. The triangle law *)
Proposition enriched_triangle_law
            {V : benabou_cosmos}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            (P : E₁ ↛e E₂)
            (Q : E₂ ↛e E₃)
  : enriched_profunctor_comp_transformation
      (lassociator_enriched_profunctor P (identity_enriched_profunctor E₂) Q)
      (rwhisker_enriched_profunctor (runitor_enriched_profunctor P) Q)
    =
    lwhisker_enriched_profunctor P (lunitor_enriched_profunctor Q).
Proof.
  use eq_enriched_profunctor_transformation ; intros z x ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro y.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  refine (!_).
  etrans.
  {
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  use is_inj_internal_transpose.
  use from_comp_enriched_profunctor_eq.
  intros y'.
  use internal_funext.
  intros v h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear v h.
  unfold internal_transpose.
  rewrite !internal_beta.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_comp_id_l.
    apply maponpaths.
    apply lunitor_enriched_profunctor_mor_comm.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  unfold lassociator_enriched_profunctor_mor_ob.
  etrans.
  {
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    rewrite !assoc'.
    do 2 apply maponpaths.
    apply (rwhisker_enriched_profunctor_mor_comm (runitor_enriched_profunctor P)).
  }
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    do 2 apply maponpaths_2.
    apply runitor_enriched_profunctor_mor_comm.
  }
  rewrite tensor_comp_id_r.
  rewrite !assoc'.
  rewrite comp_enriched_profunctor_comm.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_comp_id_l.
  rewrite !assoc.
  refine (_ @ id_left _).
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    apply sym_mon_hexagon_lassociator.
  }
  rewrite !assoc'.
  rewrite <- tensor_comp_id_l.
  rewrite sym_mon_braiding_inv.
  rewrite tensor_id_id.
  rewrite id_right.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_inv.
    rewrite tensor_id_id.
    rewrite id_left.
    apply idpath.
  }
  apply mon_rassociator_lassociator.
Qed.

(** * 3. The pentagon law *)
Proposition enriched_pentagon_law
            {V : benabou_cosmos}
            {C₁ C₂ C₃ C₄ C₅ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {E₄ : enrichment C₄ V}
            {E₅ : enrichment C₅ V}
            (P₁ : E₁ ↛e E₂)
            (P₂ : E₂ ↛e E₃)
            (P₃ : E₃ ↛e E₄)
            (P₄ : E₄ ↛e E₅)
  : enriched_profunctor_comp_transformation
      (enriched_profunctor_comp_transformation
         (lwhisker_enriched_profunctor
            P₁
            (lassociator_enriched_profunctor P₂ P₃ P₄))
         (lassociator_enriched_profunctor
            P₁
            (comp_enriched_profunctor P₂ P₃) P₄))
      (rwhisker_enriched_profunctor
         (lassociator_enriched_profunctor P₁ P₂ P₃)
         P₄)
    =
    enriched_profunctor_comp_transformation
      (lassociator_enriched_profunctor P₁ P₂ (comp_enriched_profunctor P₃ P₄))
      (lassociator_enriched_profunctor (comp_enriched_profunctor P₁ P₂) P₃ P₄).
Proof.
  use eq_enriched_profunctor_transformation ; intros z v ; cbn.
  use from_comp_enriched_profunctor_eq.
  intro w.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lwhisker_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  use is_inj_internal_lam.
  use from_comp_enriched_profunctor_eq.
  intros x.
  use internal_funext.
  intros a h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear a h.
  rewrite !internal_beta.
  rewrite !assoc.
  rewrite <- tensor_comp_id_r.
  etrans.
  {
    apply maponpaths_2.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply (lassociator_enriched_profunctor_data_comm (comp_enriched_profunctor P₁ P₂)).
  }
  etrans.
  {
    rewrite !assoc.
    do 2 apply maponpaths_2.
    rewrite !assoc'.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc.
    apply idpath.
  }
  use is_inj_internal_lam.
  use is_inj_internal_transpose.
  use from_comp_enriched_profunctor_eq.
  intros y.
  use internal_funext.
  intros a h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear a h.
  unfold internal_transpose.
  rewrite !internal_beta.
  rewrite !assoc.
  rewrite tensor_sym_mon_braiding.
  rewrite !assoc'.
  apply maponpaths.
  use internal_funext.
  intros a h.
  rewrite !tensor_comp_r_id_r.
  rewrite !(tensor_split (_ #⊗ _) h).
  rewrite !assoc'.
  apply maponpaths.
  clear a h.
  rewrite !internal_beta.
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite tensor_id_id.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    apply idpath.
  }
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite tensor_rassociator.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_id_r.
    etrans.
    {
      do 3 apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      apply lassociator_enriched_profunctor_data_comm.
    }
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_r.
      apply lassociator_enriched_profunctor_mor_comm.
    }
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc'.
    do 3 rewrite tensor_comp_id_r.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply (lassociator_enriched_profunctor_mor_comm
             P₁ (comp_enriched_profunctor P₂ P₃) P₄).
  }
  etrans.
  {
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_inv.
    rewrite tensor_id_id.
    rewrite id_left.
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply (rwhisker_enriched_profunctor_mor_comm
             (lassociator_enriched_profunctor P₁ P₂ P₃)).
  }
  etrans.
  {
    do 4 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    do 2 apply maponpaths_2.
    apply lassociator_enriched_profunctor_data_comm.
  }
  etrans.
  {
    do 3 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    do 2 apply maponpaths_2.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    apply lassociator_enriched_profunctor_mor_comm.
  }
  etrans.
  {
    unfold lassociator_enriched_profunctor_mor_ob.
    do 3 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    rewrite !assoc'.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !tensor_comp_id_r.
    apply idpath.
  }
  rewrite !assoc.
  do 3 apply maponpaths_2.
  rewrite !assoc'.
  rewrite mon_rassociator_rassociator.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_sym_mon_braiding.
  apply idpath.
Qed.
