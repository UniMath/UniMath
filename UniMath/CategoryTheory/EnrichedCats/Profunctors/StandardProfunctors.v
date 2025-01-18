(******************************************************************************************

 Standard examples of enriched profunctors

 In this file, we define standard standard constructions on enriched profunctors. One of
 the constructions is given by  the identity profunctor, which is necessary to construct
 the (double) (bi)category of enriched categories. Another is given by representable
 profunctors, and those are needed to construct an equipment. Finally, we consider
 precomposition with enriched functors, and that is needed to define squares of profunctors
 in terms of enriched natural transformations.

 Contents
 1. Identity profunctor
 2. Representable profunctors
 2.1. Left representable
 2.2. Right representable
 3. Precomposition with enriched functors

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Identity profunctor *)
Section IdentityProfunctor.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V).

  Definition identity_enriched_profunctor_data
    : enriched_profunctor_data E E.
  Proof.
    use make_enriched_profunctor_data.
    - exact (λ x y, E ⦃ x , y ⦄).
    - exact (λ x₁ x₂ y, sym_mon_braiding V _ _ · enriched_comp _ _ _ _).
    - exact (λ x y₁ y₂, enriched_comp _ _ _ _).
  Defined.

  Proposition identity_enriched_profunctor_laws
    : enriched_profunctor_laws identity_enriched_profunctor_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      apply sym_mon_braiding_runitor.
    - intros x y ; cbn.
      rewrite <- enrichment_id_left.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      etrans.
      {
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_sym_mon_braiding.
      apply maponpaths_2.
      apply sym_mon_tensor_rassociator.
    - intros x y₁ y₂ y₃ ; cbn.
      rewrite enrichment_assoc.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite enrichment_assoc'.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition identity_enriched_profunctor
    : E ↛e E.
  Proof.
    use make_enriched_profunctor.
    - exact identity_enriched_profunctor_data.
    - exact identity_enriched_profunctor_laws.
  Defined.

  Proposition identity_enriched_profunctor_lmap_e_arr
              (y : C)
              {x₁ x₂ : C}
              (g : x₁ --> x₂)
    : lmap_e_arr identity_enriched_profunctor y g
      =
      precomp_arr E y g.
  Proof.
    unfold lmap_e_arr ; cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      rewrite sym_mon_braiding_linvunitor.
      apply idpath.
    }
    apply idpath.
  Qed.

  Proposition identity_enriched_profunctor_rmap_e_arr
              {y₁ y₂ : C}
              (f : y₁ --> y₂)
              (x : C)
    : rmap_e_arr identity_enriched_profunctor f x
      =
      postcomp_arr E x f.
  Proof.
    apply idpath.
  Qed.
End IdentityProfunctor.

(** * 2. Representable profunctors *)
Section Representable.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (EF : functor_enrichment F E₁ E₂).

  (** ** 2.1. Left representable *)
  Definition representable_enriched_profunctor_left_data
    : enriched_profunctor_data E₁ E₂.
  Proof.
    use make_enriched_profunctor_data.
    - exact (λ x y, E₂ ⦃ x , F y ⦄).
    - exact (λ x₁ x₂ y, sym_mon_braiding V _ _ · enriched_comp E₂ _ _ _).
    - exact (λ x y₁ y₂, (EF y₁ y₂ #⊗ identity _) · enriched_comp E₂ _ _ _).
  Defined.

  Proposition representable_enriched_profunctor_left_laws
    : enriched_profunctor_laws
        representable_enriched_profunctor_left_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      apply sym_mon_braiding_runitor.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite functor_enrichment_id.
      rewrite <- enrichment_id_left.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      etrans.
      {
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_sym_mon_braiding.
      apply maponpaths_2.
      apply sym_mon_tensor_rassociator.
    - intros x y₁ y₂ y₃ ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite functor_enrichment_comp.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite enrichment_assoc.
      rewrite !assoc.
      rewrite tensor_lassociator.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_mor.
      rewrite !id_right.
      rewrite id_left.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- tensor_id_id.
      rewrite tensor_rassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_left
    : E₁ ↛e E₂.
  Proof.
    use make_enriched_profunctor.
    - exact representable_enriched_profunctor_left_data.
    - exact representable_enriched_profunctor_left_laws.
  Defined.

  (** ** 2.2. Right representable *)
  Definition representable_enriched_profunctor_right_data
    : enriched_profunctor_data E₂ E₁.
  Proof.
    use make_enriched_profunctor_data.
    - exact (λ x y, E₂ ⦃ F x , y ⦄).
    - exact (λ x₁ x₂ y,
             sym_mon_braiding V _ _
             · (identity _ #⊗ EF x₂ x₁)
             · enriched_comp _ _ _ _).
    - exact (λ x y₁ y₂, enriched_comp _ _ _ _).
  Defined.

  Proposition representable_enriched_profunctor_right_laws
    : enriched_profunctor_laws
        representable_enriched_profunctor_right_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite functor_enrichment_id.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      apply sym_mon_braiding_runitor.
    - intros x y ; cbn.
      rewrite <- enrichment_id_left.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      etrans.
      {
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite functor_enrichment_comp.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite <- tensor_split'.
        rewrite tensor_comp_r_id_r.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_rassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      rewrite !assoc'.
      apply maponpaths.
      rewrite sym_mon_tensor_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite mon_lassociator_rassociator.
      rewrite id_right.
      apply idpath.
    - intros x y₁ y₂ y₃ ; cbn.
      rewrite enrichment_assoc.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite enrichment_assoc'.
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
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite tensor_rassociator.
      rewrite !assoc.
      rewrite tensor_id_id.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite sym_mon_tensor_lassociator.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition representable_enriched_profunctor_right
    : E₂ ↛e E₁.
  Proof.
    use make_enriched_profunctor.
    - exact representable_enriched_profunctor_right_data.
    - exact representable_enriched_profunctor_right_laws.
  Defined.
End Representable.

(** * 3. Precomposition with enriched functors *)
Section Precomposition.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ C₁' C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₁' : enrichment C₁' V}
          {E₂' : enrichment C₂' V}
          (EF : functor_enrichment F E₁ E₁')
          (EG : functor_enrichment G E₂ E₂')
          (P : E₁' ↛e E₂').

  Definition precomp_enriched_profunctor_data
    : enriched_profunctor_data E₁ E₂.
  Proof.
    use make_enriched_profunctor_data.
    - exact (λ x y, P (G x) (F y)).
    - exact (λ x₁ x₂ y,
             (EG x₂ x₁ #⊗ identity _) · lmap_e P (G x₁) (G x₂) (F y)).
    - exact (λ x y₁ y₂,
             (EF y₁ y₂ #⊗ identity _) · rmap_e P (G x) (F y₁) (F y₂)).
  Defined.

  Proposition precomp_enriched_profunctor_laws
    : enriched_profunctor_laws precomp_enriched_profunctor_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite functor_enrichment_id.
      rewrite lmap_e_id.
      apply idpath.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite functor_enrichment_id.
      rewrite rmap_e_id.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite !assoc'.
      rewrite functor_enrichment_comp.
      rewrite !assoc.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite lmap_e_comp'.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite <- tensor_split.
        rewrite tensor_comp_l_id_r.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_lassociator.
      apply maponpaths_2.
      rewrite <- tensor_comp_id_r.
      apply maponpaths_2.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite sym_mon_braiding_inv.
      rewrite id_right.
      apply idpath.
    - intros x y₁ y₂ y₃ ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite !assoc'.
      rewrite functor_enrichment_comp.
      rewrite !assoc.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite rmap_e_comp.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite <- tensor_split.
        rewrite tensor_comp_l_id_r.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_lassociator.
      apply maponpaths_2.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite lmap_e_rmap_e'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 4 apply maponpaths_2.
          rewrite <- tensor_comp_mor.
          rewrite id_left.
          rewrite id_right.
          apply idpath.
        }
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
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
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_split.
        rewrite tensor_comp_l_id_r.
        apply idpath.
      }
      rewrite !assoc.
      apply idpath.
  Qed.

  Definition precomp_enriched_profunctor
    : E₁ ↛e E₂.
  Proof.
    use make_enriched_profunctor.
    - exact precomp_enriched_profunctor_data.
    - exact precomp_enriched_profunctor_laws.
  Defined.
End Precomposition.
