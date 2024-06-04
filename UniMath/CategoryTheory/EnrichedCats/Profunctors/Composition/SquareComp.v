(*****************************************************************************************

 Composition of squares of profunctors

 In this file we define the vertical composition of squares of profunctors.

 Content
 1. The data
 2. The laws
 3. Composition of squares

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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section CompositionSquare.
  Context {V : benabou_cosmos}
          {C₁ C₂ C₃ C₁' C₂' C₃' : category}
          {F₁ : C₁ ⟶ C₁'}
          {F₂ : C₂ ⟶ C₂'}
          {F₃ : C₃ ⟶ C₃'}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          {E₁' : enrichment C₁' V}
          {E₂' : enrichment C₂' V}
          {E₃' : enrichment C₃' V}
          {EF₁ : functor_enrichment F₁ E₁ E₁'}
          {EF₂ : functor_enrichment F₂ E₂ E₂'}
          {EF₃ : functor_enrichment F₃ E₃ E₃'}
          {P₁ : E₁ ↛e E₂}
          {P₂ : E₂ ↛e E₃}
          {Q₁ : E₁' ↛e E₂'}
          {Q₂ : E₂' ↛e E₃'}
          (τ : enriched_profunctor_square EF₁ EF₂ P₁ Q₁)
          (θ : enriched_profunctor_square EF₂ EF₃ P₂ Q₂).

  Proposition comp_v_enriched_profunctor_square_mor_eq
              (z : C₃)
              (y₁ y₂ : C₂)
              (x : C₁)
    : lmap_e P₁ y₂ y₁ x #⊗ identity _
      · (τ y₁ x #⊗ θ z y₁
      · comp_enriched_profunctor_in Q₁ Q₂ (F₃ z) (F₁ x) (F₂ y₁))
      =
      sym_mon_braiding _ _ _ #⊗ identity _
      · mon_lassociator _ _ _
      · identity _ #⊗ rmap_e P₂ z y₁ y₂
      · (τ y₂ x #⊗ θ z y₂
      · comp_enriched_profunctor_in Q₁ Q₂ (F₃ z) (F₁ x) (F₂ y₂)).
  Proof.
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      rewrite <- enriched_profunctor_transformation_lmap_e.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      rewrite <- enriched_profunctor_transformation_rmap_e.
      apply idpath.
    }
    cbn.
    refine (!_).
    etrans.
    {
      rewrite tensor_comp_r_id_r.
      rewrite !tensor_comp_id_r.
      rewrite !assoc'.
      rewrite comp_enriched_profunctor_comm.
      apply idpath.
    }
    rewrite !tensor_comp_id_l.
    rewrite tensor_comp_l_id_l.
    rewrite tensor_comp_l_id_r.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      do 4 apply maponpaths_2.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite <- tensor_split.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_lassociator.
      rewrite !assoc.
      rewrite tensor_id_id.
      rewrite <- tensor_split'.
      rewrite tensor_split.
      apply idpath.
    }
    etrans.
    {
      rewrite !assoc'.
      rewrite <- tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_comp_id_r.
      rewrite <- tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply sym_mon_hexagon_lassociator.
    }
    rewrite !assoc'.
    rewrite <- tensor_comp_id_l.
    rewrite sym_mon_braiding_inv.
    rewrite tensor_id_id.
    rewrite id_right.
    apply idpath.
  Qed.

  (** * 1. The data *)
  Definition comp_v_enriched_profunctor_square_mor
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor P₁ P₂)
        (precomp_enriched_profunctor
           EF₁ EF₃
           (comp_enriched_profunctor Q₁ Q₂)).
  Proof.
    intros z x ; cbn.
    use from_comp_enriched_profunctor_ob.
    - exact (λ y, (τ y x #⊗ θ z y) · comp_enriched_profunctor_in _ _ (F₃ z) (F₁ x) (F₂ y)).
    - intros y₁ y₂ ; cbn.
      exact (comp_v_enriched_profunctor_square_mor_eq z y₁ y₂ x).
  Defined.

  Proposition comp_v_enriched_profunctor_square_mor_comm
              (z : C₃)
              (y : C₂)
              (x : C₁)
    : comp_enriched_profunctor_in _ _ _ _ _
      · comp_v_enriched_profunctor_square_mor z x
      =
      (τ y x #⊗ θ z y)
      · comp_enriched_profunctor_in _ _ (F₃ z) (F₁ x) (F₂ y).
  Proof.
    unfold comp_v_enriched_profunctor_square_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  (** * 2. The laws *)
  Proposition comp_v_enriched_profunctor_square_laws
    : enriched_profunctor_transformation_laws
        comp_v_enriched_profunctor_square_mor.
  Proof.
    split.
    - intros z₁ z₂ x.
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
        rewrite <- tensor_comp_id_l.
        rewrite comp_v_enriched_profunctor_square_mor_comm.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        cbn.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        apply comp_enriched_profunctor_lmap_comm.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        apply id_left.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_l_id_l.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        cbn.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite comp_enriched_profunctor_lmap_comm.
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite comp_v_enriched_profunctor_square_mor_comm.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      apply maponpaths.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- enriched_profunctor_transformation_lmap_e.
      cbn.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    - intros z x₁ x₂.
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
        rewrite <- tensor_comp_id_l.
        rewrite comp_v_enriched_profunctor_square_mor_comm.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        cbn.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        apply comp_enriched_profunctor_rmap_comm.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        apply id_left.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        cbn.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite comp_enriched_profunctor_rmap_comm.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc'.
        apply idpath.
      }
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      rewrite !assoc'.
      apply maponpaths.
      rewrite comp_v_enriched_profunctor_square_mor_comm.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      apply maponpaths_2.
      rewrite <- enriched_profunctor_transformation_rmap_e.
      cbn.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
  Qed.

  (** * 3. Composition of squares *)
  Definition comp_v_enriched_profunctor_square
    : enriched_profunctor_square
        EF₁ EF₃
        (comp_enriched_profunctor P₁ P₂)
        (comp_enriched_profunctor Q₁ Q₂).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact comp_v_enriched_profunctor_square_mor.
    - exact comp_v_enriched_profunctor_square_laws.
  Defined.
End CompositionSquare.
