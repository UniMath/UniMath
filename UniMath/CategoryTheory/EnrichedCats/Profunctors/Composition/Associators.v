(******************************************************************************************

 The associators for composition of enriched profunctors

 In this file, we define the associators for composition of enriched profunctors. All the
 constructions and proofs boil down to calculations with coends. To construct the desired
 morphisms, we use the mapping property and to prove the necessary laws, we use the
 uniqueness of such morphisms.

 Content
 1. The left associator
 1.1. Action on objects
 1.2. The data
 1.3. The laws
 1.4. The left associator as a transformation
 2. The right associator
 2.1. Action on objects
 2.2. The data

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

Section Associator.
  Context {V : benabou_cosmos}
          {C₁ C₂ C₃ C₄ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          {E₄ : enrichment C₄ V}
          (P₁ : E₁ ↛e E₂)
          (P₂ : E₂ ↛e E₃)
          (P₃ : E₃ ↛e E₄).

  (** * 1. The left associator *)

  (** ** 1.1. Action on objects *)
  Definition lassociator_enriched_profunctor_mor_ob
             (z : C₄)
             (y : C₃)
             (x : C₂)
             (w : C₁)
    : P₂ y x ⊗ P₃ z y ⊗ P₁ x w
      -->
      comp_enriched_profunctor (comp_enriched_profunctor P₁ P₂) P₃ z w
    := sym_mon_braiding _ _ _
       · mon_rassociator _ _ _
       · (comp_enriched_profunctor_in P₁ P₂ y w x #⊗ identity _)
       · comp_enriched_profunctor_in (comp_enriched_profunctor P₁ P₂) P₃ z w y.

  Proposition lassociator_enriched_profunctor_mor_eq
              (z : C₄)
              {y₁ y₂ : C₃}
              (g : y₁ --> y₂)
              (x : C₂)
              (w : C₁)
    : identity (P₂ y₂ x) #⊗ rmap_e_arr P₃ g z
      · internal_lam (lassociator_enriched_profunctor_mor_ob z y₂ x w)
      =
      lmap_e_arr P₂ x g #⊗ identity (P₃ z y₁)
      · internal_lam (lassociator_enriched_profunctor_mor_ob z y₁ x w).
  Proof.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    rewrite !(tensor_split (_ #⊗ _) h).
    rewrite !assoc'.
    apply maponpaths.
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    rewrite !tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite !tensor_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_id_id.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      rewrite !assoc'.
      apply maponpaths.
      apply (comp_enriched_profunctor_comm (comp_enriched_profunctor P₁ P₂) P₃).
    }
    rewrite !assoc.
    rewrite <- !tensor_comp_id_r.
    do 2 apply maponpaths_2.
    apply comp_enriched_profunctor_lmap_e_arr.
  Qed.

  (** ** 1.2. The data *)
  Definition lassociator_enriched_profunctor_mor
             (z : C₄)
             (x : C₂)
             (w : C₁)
    : comp_enriched_profunctor_ob P₂ P₃ z x
      -->
      P₁ x w ⊸ comp_enriched_profunctor (comp_enriched_profunctor P₁ P₂) P₃ z w.
  Proof.
    use from_comp_enriched_profunctor_ob.
    - exact (λ y, internal_lam (lassociator_enriched_profunctor_mor_ob z y x w)).
    - exact (λ _ _ g, lassociator_enriched_profunctor_mor_eq z g x w).
  Defined.

  Proposition lassociator_enriched_profunctor_mor_comm
              (z : C₄)
              (y : C₃)
              (x : C₂)
              (w : C₁)
    : (comp_enriched_profunctor_in _ _ z x y
       · lassociator_enriched_profunctor_mor z x w) #⊗ identity _
       · internal_eval _ _
      =
      lassociator_enriched_profunctor_mor_ob z y x w.
  Proof.
    unfold lassociator_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition lassociator_enriched_profunctor_data_eq
              (z : C₄)
              {x₁ x₂ : C₂}
              (f : x₁ --> x₂)
              (w : C₁)
    : identity _ #⊗ rmap_e_arr (comp_enriched_profunctor P₂ P₃) f z
      · (sym_mon_braiding V (P₁ x₂ w) (comp_enriched_profunctor_ob P₂ P₃ z x₂)
      · lassociator_enriched_profunctor_mor z x₂ w #⊗ identity _
      · internal_eval _ _)
      =
      lmap_e_arr P₁ w f #⊗ identity _
      · (sym_mon_braiding V (P₁ x₁ w) (comp_enriched_profunctor_ob P₂ P₃ z x₁)
      · lassociator_enriched_profunctor_mor z x₁ w #⊗ identity _
      · internal_eval _ _).
  Proof.
    use is_inj_internal_transpose.
    use from_comp_enriched_profunctor_eq.
    intros x'.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
    rewrite !assoc'.
    apply maponpaths.
    unfold internal_transpose.
    rewrite !internal_beta.
    rewrite !assoc.
    rewrite !tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply comp_enriched_profunctor_rmap_e_arr.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite !assoc'.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite lassociator_enriched_profunctor_mor_comm.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      apply lassociator_enriched_profunctor_mor_comm.
    }
    apply maponpaths.
    unfold lassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !tensor_sym_mon_braiding.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_id_id.
    rewrite !tensor_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- !tensor_comp_id_r.
    apply maponpaths_2.
    rewrite comp_enriched_profunctor_comm.
    apply idpath.
  Qed.

  Definition lassociator_enriched_profunctor_data
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor P₁ (comp_enriched_profunctor P₂ P₃))
        (comp_enriched_profunctor (comp_enriched_profunctor P₁ P₂) P₃).
  Proof.
    intros z w.
    use from_comp_enriched_profunctor_ob.
    - exact (λ x,
             sym_mon_braiding _ _ _
             · (lassociator_enriched_profunctor_mor z x w #⊗ identity _)
             · internal_eval _ _).
    - exact (λ _ _ f, lassociator_enriched_profunctor_data_eq z f w).
  Defined.

  Proposition lassociator_enriched_profunctor_data_comm
              (z : C₄)
              (x : C₂)
              (w : C₁)
    : comp_enriched_profunctor_in _ _ z w x
      · lassociator_enriched_profunctor_data z w
      =
      sym_mon_braiding _ _ _
      · (lassociator_enriched_profunctor_mor z x w #⊗ identity _)
      · internal_eval _ _.
  Proof.
    unfold lassociator_enriched_profunctor_data.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  (** ** 1.3. The laws *)
  Proposition lassociator_enriched_profunctor_laws
    : enriched_profunctor_transformation_laws
        lassociator_enriched_profunctor_data.
  Proof.
    split.
    - intros z₁ z₂ w ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros x.
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
        rewrite <- !tensor_comp_id_l.
        rewrite lassociator_enriched_profunctor_data_comm.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply comp_enriched_profunctor_lmap_comm.
      }
      rewrite !assoc'.
      apply maponpaths.
      use is_inj_internal_lam.
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
      use internal_funext.
      intros v h.
      rewrite !tensor_comp_r_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      rewrite !assoc'.
      apply maponpaths.
      clear v h.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite !tensor_sym_mon_braiding.
      etrans.
      {
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc'.
        rewrite lassociator_enriched_profunctor_data_comm.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        cbn.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          apply comp_enriched_profunctor_lmap_comm.
        }
        rewrite <- tensor_comp_id_r.
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_lmap_mor.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        apply lassociator_enriched_profunctor_mor_comm.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        rewrite <- tensor_comp_id_r.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        unfold lassociator_enriched_profunctor_mor_ob.
        apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite sym_mon_braiding_inv.
        apply id_right.
      }
      etrans.
      {
        rewrite !tensor_comp_id_l.
        rewrite !assoc'.
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        apply idpath.
      }
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        rewrite <- tensor_comp_id_r.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_id_r.
        rewrite lassociator_enriched_profunctor_mor_comm.
        unfold lassociator_enriched_profunctor_mor_ob.
        rewrite !assoc'.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        apply (comp_enriched_profunctor_lmap_comm (comp_enriched_profunctor P₁ P₂) P₃).
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_id_id.
      do 3 apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_rassociator.
      rewrite tensor_id_id.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite sym_mon_braiding_inv.
        apply id_right.
      }
      refine (_ @ id_left _).
      rewrite <- tensor_id_id.
      rewrite <- mon_rassociator_lassociator.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- mon_lassociator_lassociator.
      rewrite !assoc'.
      rewrite mon_lassociator_rassociator.
      rewrite id_right.
      apply idpath.
    - intros z₁ z₂ w ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros x.
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
        rewrite <- !tensor_comp_id_l.
        rewrite lassociator_enriched_profunctor_data_comm.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply comp_enriched_profunctor_rmap_comm.
      }
      rewrite !assoc'.
      apply maponpaths.
      use is_inj_internal_lam.
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
      use internal_funext.
      intros v h.
      rewrite !tensor_comp_r_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_split.
      }
      refine (!_).
      rewrite !assoc'.
      apply maponpaths.
      clear v h.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite !tensor_sym_mon_braiding.
      etrans.
      {
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc'.
        rewrite lassociator_enriched_profunctor_data_comm.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        apply lassociator_enriched_profunctor_mor_comm.
      }
      unfold lassociator_enriched_profunctor_mor_ob.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        apply idpath.
      }
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        rewrite <- tensor_comp_id_r.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_id_r.
        rewrite lassociator_enriched_profunctor_mor_comm.
        unfold lassociator_enriched_profunctor_mor_ob.
        rewrite !assoc'.
        do 2 rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        apply (comp_enriched_profunctor_rmap_comm (comp_enriched_profunctor P₁ P₂) P₃).
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        cbn.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply comp_enriched_profunctor_rmap_comm.
      }
      etrans.
      {
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !tensor_comp_id_r.
        rewrite !assoc.
        apply idpath.
      }
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_right.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- mon_rassociator_rassociator.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite sym_mon_braiding_inv.
      rewrite id_right.
      apply idpath.
  Qed.

  (** ** 1.4. The left associator as a transformation *)
  Definition lassociator_enriched_profunctor
    : enriched_profunctor_transformation
        (comp_enriched_profunctor
           P₁
           (comp_enriched_profunctor P₂ P₃))
        (comp_enriched_profunctor
           (comp_enriched_profunctor P₁ P₂)
           P₃).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact lassociator_enriched_profunctor_data.
    - exact lassociator_enriched_profunctor_laws.
  Defined.

  (** * 2. The right associator *)

  (** ** 2.1. Action on objects *)
  Definition rassociator_enriched_profunctor_mor_ob
             (z : C₄)
             (y : C₃)
             (x : C₂)
             (w : C₁)
    : P₁ x w ⊗ P₂ y x ⊗ P₃ z y
      -->
      comp_enriched_profunctor P₁ (comp_enriched_profunctor P₂ P₃) z w
    := mon_lassociator _ _ _
       · (identity _ #⊗ comp_enriched_profunctor_in P₂ P₃ z x y)
       · comp_enriched_profunctor_in P₁ (comp_enriched_profunctor P₂ P₃) z w x.

  Proposition rassociator_enriched_profunctor_mor_eq
              (z : C₄)
              (y : C₃)
              {x₁ x₂ : C₂}
              (g : x₁ --> x₂)
              (w : C₁)
    : identity _ #⊗ rmap_e_arr P₂ g y
      · internal_lam (rassociator_enriched_profunctor_mor_ob z y x₂ w)
      =
      lmap_e_arr P₁ w g #⊗ identity _
      · internal_lam (rassociator_enriched_profunctor_mor_ob z y x₁ w).
  Proof.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    rewrite !(tensor_split (_ #⊗ _) h).
    rewrite !assoc'.
    apply maponpaths.
    unfold rassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    rewrite !tensor_lassociator.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_id_id.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      apply (comp_enriched_profunctor_comm P₁ (comp_enriched_profunctor P₂ P₃)).
    }
    rewrite !assoc.
    rewrite <- !tensor_comp_id_l.
    apply maponpaths_2.
    apply maponpaths.
    apply comp_enriched_profunctor_rmap_e_arr.
  Qed.

  (** ** 2.2. The data *)
  Definition rassociator_enriched_profunctor_mor
             (z : C₄)
             (y : C₃)
             (w : C₁)
    : comp_enriched_profunctor P₁ P₂ y w
      -->
      P₃ z y ⊸ comp_enriched_profunctor P₁ (comp_enriched_profunctor P₂ P₃) z w.
  Proof.
    use from_comp_enriched_profunctor_ob.
    - exact (λ x, internal_lam (rassociator_enriched_profunctor_mor_ob z y x w)).
    - exact (λ _ _ g, rassociator_enriched_profunctor_mor_eq z y g w).
  Defined.

  Proposition rassociator_enriched_profunctor_mor_comm
              (z : C₄)
              (y : C₃)
              (x : C₂)
              (w : C₁)
    : (comp_enriched_profunctor_in _ _ y w x
       · rassociator_enriched_profunctor_mor z y w) #⊗ identity _
       · internal_eval _ _
      =
      rassociator_enriched_profunctor_mor_ob z y x w.
  Proof.
    unfold rassociator_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition rassociator_enriched_profunctor_data_eq
              (z : C₄)
              {y₁ y₂ : C₃}
              (g : y₁ --> y₂)
              (w : C₁)
    : identity _ #⊗ rmap_e_arr P₃ g z
      · (rassociator_enriched_profunctor_mor z y₂ w #⊗ identity _
      · internal_eval _ _)
      =
      lmap_e_arr (comp_enriched_profunctor P₁ P₂) w g #⊗ identity _
      · (rassociator_enriched_profunctor_mor z y₁ w #⊗ identity _
      · internal_eval _ _).
  Proof.
    use is_inj_internal_lam.
    use from_comp_enriched_profunctor_eq.
    intros x'.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !(tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
    rewrite !assoc'.
    apply maponpaths.
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
      apply rassociator_enriched_profunctor_mor_comm.
    }
    unfold rassociator_enriched_profunctor_mor_ob.
    etrans.
    {
      rewrite <- tensor_id_id.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite <- !tensor_comp_id_r.
      do 3 apply maponpaths_2.
      apply comp_enriched_profunctor_lmap_e_arr.
    }
    etrans.
    {
      rewrite !assoc'.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite rassociator_enriched_profunctor_mor_comm.
      apply idpath.
    }
    unfold rassociator_enriched_profunctor_mor_ob.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_lassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- tensor_comp_id_l.
    apply maponpaths.
    rewrite comp_enriched_profunctor_comm.
    apply idpath.
  Qed.

  Definition rassociator_enriched_profunctor_data
             (z : C₄)
             (w : C₁)
    : comp_enriched_profunctor (comp_enriched_profunctor P₁ P₂) P₃ z w
      -->
      comp_enriched_profunctor P₁ (comp_enriched_profunctor P₂ P₃) z w.
  Proof.
    use from_comp_enriched_profunctor_ob.
    - exact (λ y,
             (rassociator_enriched_profunctor_mor z y w #⊗ identity _)
             · internal_eval _ _).
    - exact (λ _ _ g, rassociator_enriched_profunctor_data_eq z g w).
  Defined.

  Proposition rassociator_enriched_profunctor_data_comm
              (z : C₄)
              (y : C₃)
              (w : C₁)
    : comp_enriched_profunctor_in _ _ z w y
      · rassociator_enriched_profunctor_data z w
      =
      (rassociator_enriched_profunctor_mor z y w #⊗ identity _)
      · internal_eval _ _.
  Proof.
    unfold rassociator_enriched_profunctor_data.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.
End Associator.
