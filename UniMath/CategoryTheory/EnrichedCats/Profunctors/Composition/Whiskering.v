(******************************************************************************************

 Whiskering of transformations of enriched profunctors

 We define the whiskering operations for transformations of enriched profunctors. The
 constructions and proofs boil down to calculations with coends. To construct the desired
 morphisms, we use the mapping property and to prove the necessary laws, we use the
 uniqueness of such morphisms.

 Content
 1. Right whiskering
 2. Left whiskering

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coends.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.CompositionProf.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Right whiskering *)
Section RightWhiskering.
  Context {V : benabou_cosmos}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          {P₁ P₂ : E₁ ↛e E₂}
          (τ : enriched_profunctor_transformation P₁ P₂)
          (Q : E₂ ↛e E₃).

  Proposition rwhisker_enriched_profunctor_mor_eq
              (z : C₃)
              (y₁ y₂ : C₂)
              (x : C₁)
    : lmap_e P₁ y₂ y₁ x #⊗ identity _
      · (τ y₁ x #⊗ identity _ · comp_enriched_profunctor_in P₂ Q z x y₁)
      =
      sym_mon_braiding _ _ _ #⊗ identity _
      · mon_lassociator _ _ _
      · identity _ #⊗ rmap_e Q z y₁ y₂
      · (τ y₂ x #⊗ identity _
       · comp_enriched_profunctor_in P₂ Q z x y₂).
  Proof.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite <- enriched_profunctor_transformation_lmap_e.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    rewrite comp_enriched_profunctor_comm.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite <- tensor_split.
      apply tensor_split'.
    }
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      rewrite !assoc'.
      rewrite <- tensor_id_id.
      rewrite <- tensor_lassociator.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite <- tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite sym_mon_tensor_lassociator'.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite mon_rassociator_lassociator.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition rwhisker_enriched_profunctor_mor
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor P₁ Q)
        (comp_enriched_profunctor P₂ Q).
  Proof.
    intros z x.
    use from_comp_enriched_profunctor_ob.
    - exact (λ y, (τ y x #⊗ identity _) · comp_enriched_profunctor_in _ _ z x y).
    - intros y₁ y₂ ; cbn.
      exact (rwhisker_enriched_profunctor_mor_eq z y₁ y₂ x).
  Defined.

  Proposition rwhisker_enriched_profunctor_mor_comm
              (z : C₃)
              (y : C₂)
              (x : C₁)
    : comp_enriched_profunctor_in _ _ z x y · rwhisker_enriched_profunctor_mor z x
      =
      (τ y x #⊗ identity _) · comp_enriched_profunctor_in _ _ z x y.
  Proof.
    unfold rwhisker_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  Proposition rwhisker_enriched_profunctor_laws
    : enriched_profunctor_transformation_laws
        rwhisker_enriched_profunctor_mor.
  Proof.
    split.
    - intros z₁ z₂ x ; cbn.
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
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_l.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite rwhisker_enriched_profunctor_mor_comm.
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_lmap_comm.
        unfold comp_enriched_profunctor_lmap_mor.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split'.
        rewrite tensor_comp_l_id_l.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comp_enriched_profunctor_lmap_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        rewrite !assoc'.
        rewrite rwhisker_enriched_profunctor_mor_comm.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        apply idpath.
      }
      apply idpath.
    - intros z x₁ x₂ ; cbn.
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
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_l.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite rwhisker_enriched_profunctor_mor_comm.
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_rmap_comm.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comp_enriched_profunctor_rmap_comm.
      }
      unfold comp_enriched_profunctor_rmap_mor.
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite rwhisker_enriched_profunctor_mor_comm.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_r.
      apply maponpaths_2.
      rewrite enriched_profunctor_transformation_rmap_e.
      apply idpath.
  Qed.

  Definition rwhisker_enriched_profunctor
    : enriched_profunctor_transformation
        (comp_enriched_profunctor P₁ Q)
        (comp_enriched_profunctor P₂ Q).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact rwhisker_enriched_profunctor_mor.
    - exact rwhisker_enriched_profunctor_laws.
  Defined.
End RightWhiskering.

(** * 2. Left whiskering *)
Section LeftWhiskering.
  Context {V : benabou_cosmos}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (P : E₁ ↛e E₂)
          {Q₁ Q₂ : E₂ ↛e E₃}
          (τ : enriched_profunctor_transformation Q₁ Q₂).

  Proposition lwhisker_enriched_profunctor_mor_eq
              (z : C₃)
              (y₁ y₂ : C₂)
              (x : C₁)
    : lmap_e P y₂ y₁ x #⊗ identity _
      · (identity _ #⊗ τ z y₁
      · comp_enriched_profunctor_in P Q₂ z x y₁)
      =
      sym_mon_braiding _ _ _ #⊗ identity _
      · mon_lassociator _ _ _
      · identity _ #⊗ rmap_e Q₁ z y₁ y₂
      · (identity _ #⊗ τ z y₂
      · comp_enriched_profunctor_in P Q₂ z x y₂).
  Proof.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite <- enriched_profunctor_transformation_rmap_e.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite comp_enriched_profunctor_comm'.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      rewrite <- tensor_split'.
      apply tensor_split.
    }
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_id_id.
      rewrite <- tensor_split'.
      apply tensor_split.
    }
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      rewrite !assoc.
      rewrite <- sym_mon_hexagon_lassociator.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      apply maponpaths.
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      apply id_left.
    }
    apply mon_lassociator_rassociator.
  Qed.

  Definition lwhisker_enriched_profunctor_mor
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor P Q₁)
        (comp_enriched_profunctor P Q₂).
  Proof.
    intros z x.
    use from_comp_enriched_profunctor_ob.
    - exact (λ y, (identity _ #⊗ τ z y) · comp_enriched_profunctor_in _ _ z x y).
    - intros y₁ y₂ ; cbn.
      exact (lwhisker_enriched_profunctor_mor_eq z y₁ y₂ x).
  Defined.

  Proposition lwhisker_enriched_profunctor_mor_comm
              (z : C₃)
              (y : C₂)
              (x : C₁)
    : comp_enriched_profunctor_in _ _ z x y · lwhisker_enriched_profunctor_mor z x
      =
      (identity _ #⊗ τ z y) · comp_enriched_profunctor_in _ _ z x y.
  Proof.
    unfold lwhisker_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  Proposition lwhisker_enriched_profunctor_laws
    : enriched_profunctor_transformation_laws
        lwhisker_enriched_profunctor_mor.
  Proof.
    split.
    - intros z₁ z₂ x ; cbn.
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
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_l.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite lwhisker_enriched_profunctor_mor_comm.
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_lmap_comm.
        unfold comp_enriched_profunctor_lmap_mor.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_l_id_l.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comp_enriched_profunctor_lmap_comm.
      }
      rewrite !assoc'.
      etrans.
      {
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        rewrite !assoc'.
        rewrite lwhisker_enriched_profunctor_mor_comm.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        apply idpath.
      }
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite enriched_profunctor_transformation_lmap_e.
      apply idpath.
    - intros z x₁ x₂ ; cbn.
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
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_l.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite lwhisker_enriched_profunctor_mor_comm.
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite comp_enriched_profunctor_rmap_comm.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comp_enriched_profunctor_rmap_comm.
      }
      unfold comp_enriched_profunctor_rmap_mor.
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite lwhisker_enriched_profunctor_mor_comm.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_split'.
      apply idpath.
  Qed.

  Definition lwhisker_enriched_profunctor
    : enriched_profunctor_transformation
        (comp_enriched_profunctor P Q₁)
        (comp_enriched_profunctor P Q₂).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact lwhisker_enriched_profunctor_mor.
    - exact lwhisker_enriched_profunctor_laws.
  Defined.
End LeftWhiskering.
