(******************************************************************************************

 The unitors for composition of enriched profunctors

 In this file, we define the unitors for composition of enriched profunctors. All the
 constructions and proofs boil down to calculations with coends. To construct the desired
 morphisms, we use the mapping property and to prove the necessary laws, we use the
 uniqueness of such morphisms.

 Content
 1. The left unitor
 1.1. The morphism of the left unitor
 1.2. Naturality of the left unitor
 1.3. The left unitor as a transformation
 1.4. The inverse of the left unitor
 2. The right unitor
 2.1. The morphism of the right unitor
 2.2. Naturality of the right unitor
 2.3. The right unitor as a transformation
 2.4. The inverse of the right unitor

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
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Invertible.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.CompositionProf.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section Unitors.
  Context {V : benabou_cosmos}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : E₁ ↛e E₂).

  (** * 1. The left unitor *)

  (** ** 1.1. The morphism of the left unitor *)
  Proposition lunitor_enriched_profunctor_mor_eq
              (y : C₂)
              (x x' x'' : C₁)
    : (sym_mon_braiding _ _ _ · enriched_comp E₁ x' x'' x) #⊗ identity _
      · rmap_e P y x' x
      =
      sym_mon_braiding _ _ _ #⊗ identity _
      · mon_lassociator _ _ _
      · identity _ #⊗ rmap_e P y x' x''
      · rmap_e P y x'' x.
  Proof.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite rmap_e_comp.
    rewrite !assoc.
    apply idpath.
  Qed.

  Definition lunitor_enriched_profunctor_mor
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor (identity_enriched_profunctor E₁) P) P.
  Proof.
    intros y x.
    use from_comp_enriched_profunctor_ob.
    - exact (λ x', rmap_e P _ _ _).
    - intros x' x'' ; cbn.
      exact (lunitor_enriched_profunctor_mor_eq y x x' x'').
  Defined.

  Proposition lunitor_enriched_profunctor_mor_comm
              (y : C₂)
              (x₁ x₂ : C₁)
    : comp_enriched_profunctor_in (identity_enriched_profunctor E₁) P y x₂ x₁
      · lunitor_enriched_profunctor_mor y x₂
      =
      rmap_e P y x₁ x₂.
  Proof.
    unfold lunitor_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  (** ** 1.2. Naturality of the left unitor *)
  Proposition lunitor_enriched_profunctor_laws
    : enriched_profunctor_transformation_laws
        lunitor_enriched_profunctor_mor.
  Proof.
    split.
    - intros y₁ y₂ x ; cbn.
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
        rewrite lunitor_enriched_profunctor_mor_comm.
        apply rmap_e_lmap_e.
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
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      unfold comp_enriched_profunctor_lmap_mor.
      rewrite !assoc'.
      rewrite lunitor_enriched_profunctor_mor_comm.
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator'.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      rewrite id_right.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      rewrite id_left.
      apply idpath.
    - intros x y₁ y₂ ; cbn.
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
        rewrite lunitor_enriched_profunctor_mor_comm.
        apply rmap_e_rmap_e.
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
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      unfold comp_enriched_profunctor_rmap_mor.
      rewrite !assoc'.
      rewrite lunitor_enriched_profunctor_mor_comm.
      cbn.
      apply idpath.
  Qed.

  (** ** 1.3. The left unitor as a transformation *)
  Definition lunitor_enriched_profunctor
    : enriched_profunctor_transformation
        (comp_enriched_profunctor (identity_enriched_profunctor E₁) P)
        P.
  Proof.
    use make_enriched_profunctor_transformation.
    - exact lunitor_enriched_profunctor_mor.
    - exact lunitor_enriched_profunctor_laws.
  Defined.

  Definition lunitor_enriched_profunctor_square
    : enriched_profunctor_square
        (functor_id_enrichment E₁)
        (functor_id_enrichment E₂)
        (comp_enriched_profunctor (identity_enriched_profunctor E₁) P)
        P.
  Proof.
    use enriched_profunctor_transformation_to_square.
    exact lunitor_enriched_profunctor.
  Defined.

  (** ** 1.4. The inverse of the left unitor *)
  Definition linvunitor_enriched_profunctor_mor
             (y : C₂)
             (x : C₁)
    : P y x
      -->
      comp_enriched_profunctor (identity_enriched_profunctor E₁) P y x
    := mon_linvunitor _
       · (enriched_id E₁ x #⊗ identity _)
       · comp_enriched_profunctor_in (identity_enriched_profunctor E₁) P y x x.

  Proposition is_inverse_linvunitor_enriched_profunctor_mor
              (y : C₂)
              (x : C₁)
    : is_inverse_in_precat
        (lunitor_enriched_profunctor y x)
        (linvunitor_enriched_profunctor_mor y x).
  Proof.
    split.
    - cbn.
      use from_comp_enriched_profunctor_eq.
      intros x'.
      rewrite !assoc.
      rewrite lunitor_enriched_profunctor_mor_comm.
      rewrite id_right.
      unfold linvunitor_enriched_profunctor_mor.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_linvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply (comp_enriched_profunctor_comm' (identity_enriched_profunctor E₁) P).
      }
      cbn.
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_r.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_linvunitor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- mon_linvunitor_triangle.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      rewrite mon_inv_triangle.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite <- tensor_comp_id_r.
      rewrite !assoc.
      rewrite sym_mon_braiding_rinvunitor.
      rewrite mon_linvunitor_lunitor.
      apply tensor_id_id.
    - cbn.
      unfold linvunitor_enriched_profunctor_mor.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply lunitor_enriched_profunctor_mor_comm.
      }
      rewrite rmap_e_id.
      apply mon_linvunitor_lunitor.
  Qed.

  Definition is_iso_lunitor_enriched_profunctor
    : is_iso_enriched_profunctor_transformation
        lunitor_enriched_profunctor.
  Proof.
    intros y x.
    use make_is_z_isomorphism.
    - exact (linvunitor_enriched_profunctor_mor y x).
    - exact (is_inverse_linvunitor_enriched_profunctor_mor y x).
  Defined.

  Definition linvunitor_enriched_profunctor
    : enriched_profunctor_transformation
        P
        (comp_enriched_profunctor (identity_enriched_profunctor E₁) P)
    := inv_enriched_profunctor_transformation
         _
         is_iso_lunitor_enriched_profunctor.

  Definition linvunitor_enriched_profunctor_square
    : enriched_profunctor_square
        (functor_id_enrichment E₁)
        (functor_id_enrichment E₂)
        P
        (comp_enriched_profunctor (identity_enriched_profunctor E₁) P).
  Proof.
    use enriched_profunctor_transformation_to_square.
    exact linvunitor_enriched_profunctor.
  Defined.

  (** * 2. The right unitor *)

  (** ** 2.1. The morphism of the right unitor *)
  Proposition runitor_enriched_profunctor_mor_eq
              (y y' y'' : C₂)
              (x : C₁)
    : lmap_e P y'' y' x #⊗ identity _
      · (sym_mon_braiding _ _ _
      · lmap_e P y' y x)
      =
      sym_mon_braiding _ _ _ #⊗ identity _
      · mon_lassociator _ _ _
      · identity _ #⊗ enriched_comp E₂ y y' y''
      · (sym_mon_braiding _ _ _
      · lmap_e P y'' y x).
  Proof.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      rewrite lmap_e_comp'.
      apply idpath.
    }
    rewrite !assoc.
    do 2 apply maponpaths_2.

    rewrite sym_mon_tensor_rassociator.
    do 2 apply maponpaths_2.
    refine (!(id_right _) @ _).
    rewrite <- mon_lassociator_rassociator.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply sym_mon_hexagon_lassociator.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite sym_mon_braiding_inv.
    rewrite tensor_id_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition runitor_enriched_profunctor_mor
    : enriched_profunctor_transformation_data
        (comp_enriched_profunctor P (identity_enriched_profunctor E₂))
        P.
  Proof.
    intros y x.
    use from_comp_enriched_profunctor_ob.
    - refine (λ y', sym_mon_braiding _ _ _ · lmap_e P _ _ _).
    - intros y' y'' ; cbn.
      exact (runitor_enriched_profunctor_mor_eq y y' y'' x).
  Defined.

  Proposition runitor_enriched_profunctor_mor_comm
              (y₁ y₂ : C₂)
              (x : C₁)
    : comp_enriched_profunctor_in P (identity_enriched_profunctor E₂) y₂ x y₁
      · runitor_enriched_profunctor_mor y₂ x
      =
      sym_mon_braiding _ _ _ · lmap_e P y₁ y₂ x.
  Proof.
    unfold runitor_enriched_profunctor_mor.
    rewrite from_comp_enriched_profunctor_ob_comm.
    apply idpath.
  Qed.

  (** ** 2.2. Naturality of the right unitor *)
  Proposition runitor_enriched_profunctor_laws
    : enriched_profunctor_transformation_laws
        runitor_enriched_profunctor_mor.
  Proof.
    split.
    - intros x₁ x₂ y ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y'.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite (tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
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
        rewrite runitor_enriched_profunctor_mor_comm.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite lmap_e_lmap_e.
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
      etrans.
      {
        apply maponpaths.
        unfold comp_enriched_profunctor_lmap_mor.
        rewrite !assoc.
        rewrite sym_mon_braiding_inv.
        rewrite id_left.
        rewrite !assoc'.
        do 2 apply maponpaths.
        apply from_comp_enriched_profunctor_ob_comm.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      cbn.
      rewrite !tensor_comp_id_r.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite sym_mon_tensor_lassociator'.
      refine (_ @ id_left _).
      rewrite !assoc.
      do 2 apply maponpaths_2.
      (** This makes the goal more readable *)
      generalize (E₂ ⦃ x₂, x₁ ⦄) (P y' y) (E₂ ⦃ x₁, y' ⦄).
      intros v₁ v₂ v₃.
      rewrite (sym_mon_tensor_lassociator V v₁ v₂ v₃).
      rewrite <- mon_rassociator_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      refine (_ @ id_left _).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite (sym_mon_tensor_lassociator V v₃ v₁ v₂).
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_lassociator_rassociator.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_hexagon_lassociator.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          rewrite id_left.
          apply idpath.
        }
        rewrite mon_lassociator_rassociator.
        apply id_right.
      }
      rewrite <- tensor_comp_id_r.
      rewrite sym_mon_braiding_inv.
      apply tensor_id_id.
    - intros y x₁ x₂ ; cbn.
      use is_inj_internal_transpose.
      use from_comp_enriched_profunctor_eq.
      intros y'.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite (tensor_split (comp_enriched_profunctor_in _ _ _ _ _) h).
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
        rewrite runitor_enriched_profunctor_mor_comm.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc'.
      rewrite lmap_e_rmap_e'.
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
      etrans.
      {
        apply maponpaths.
        unfold comp_enriched_profunctor_rmap_mor.
        rewrite !assoc'.
        do 3 apply maponpaths.
        apply from_comp_enriched_profunctor_ob_comm.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      cbn.
      rewrite !assoc.
      rewrite sym_mon_braiding_inv.
      rewrite id_left.
      apply maponpaths_2.
      rewrite <- sym_mon_hexagon_rassociator.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      rewrite id_right.
      apply idpath.
  Qed.

  (** ** 2.3. The right unitor as a transformation *)
  Definition runitor_enriched_profunctor
    : enriched_profunctor_transformation
        (comp_enriched_profunctor P (identity_enriched_profunctor E₂))
        P.
  Proof.
    use make_enriched_profunctor_transformation.
    - exact runitor_enriched_profunctor_mor.
    - exact runitor_enriched_profunctor_laws.
  Defined.

  Definition runitor_enriched_profunctor_square
    : enriched_profunctor_square
        (functor_id_enrichment E₁)
        (functor_id_enrichment E₂)
        (comp_enriched_profunctor P (identity_enriched_profunctor E₂))
        P.
  Proof.
    use enriched_profunctor_transformation_to_square.
    exact runitor_enriched_profunctor.
  Defined.

  (** ** 2.4. The inverse of the right unitor *)
  Definition rinvunitor_enriched_profunctor_mor
             (y : C₂)
             (x : C₁)
    : P y x --> comp_enriched_profunctor P (identity_enriched_profunctor E₂) y x
    := mon_rinvunitor _
       · (identity _ #⊗ enriched_id E₂ y)
       · comp_enriched_profunctor_in P (identity_enriched_profunctor E₂) y x y.

  Proposition is_inverse_rinvunitor_enriched_profunctor_mor
              (y : C₂)
              (x : C₁)
    : is_inverse_in_precat
        (runitor_enriched_profunctor y x)
        (rinvunitor_enriched_profunctor_mor y x).
  Proof.
    split.
    - cbn.
      use from_comp_enriched_profunctor_eq.
      intros x'.
      rewrite !assoc.
      rewrite runitor_enriched_profunctor_mor_comm.
      rewrite id_right.
      unfold rinvunitor_enriched_profunctor_mor.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        apply (comp_enriched_profunctor_comm P (identity_enriched_profunctor E₂)).
      }
      cbn.
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- mon_rinvunitor_triangle.
        etrans.
        {
          do 3 apply maponpaths_2.
          rewrite !assoc'.
          rewrite mon_rassociator_lassociator.
          apply id_right.
        }
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- mon_inv_triangle.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite sym_mon_braiding_linvunitor.
        rewrite mon_rinvunitor_runitor.
        apply tensor_id_id.
      }
      rewrite id_right.
      apply sym_mon_braiding_inv.
    - cbn.
      unfold rinvunitor_enriched_profunctor_mor.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply runitor_enriched_profunctor_mor_comm.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite lmap_e_id.
        apply idpath.
      }
      rewrite !assoc.
      rewrite sym_mon_braiding_rinvunitor.
      apply mon_linvunitor_lunitor.
  Qed.

  Definition is_iso_runitor_enriched_profunctor
    : is_iso_enriched_profunctor_transformation
        runitor_enriched_profunctor.
  Proof.
    intros y x.
    use make_is_z_isomorphism.
    - exact (rinvunitor_enriched_profunctor_mor y x).
    - exact (is_inverse_rinvunitor_enriched_profunctor_mor y x).
  Defined.

  Definition rinvunitor_enriched_profunctor
    : enriched_profunctor_transformation
        P
        (comp_enriched_profunctor P (identity_enriched_profunctor E₂))
    := inv_enriched_profunctor_transformation
         _
         is_iso_runitor_enriched_profunctor.

  Definition rinvunitor_enriched_profunctor_square
    : enriched_profunctor_square
        (functor_id_enrichment E₁)
        (functor_id_enrichment E₂)
        P
        (comp_enriched_profunctor P (identity_enriched_profunctor E₂)).
  Proof.
    use enriched_profunctor_transformation_to_square.
    exact rinvunitor_enriched_profunctor.
  Defined.
End Unitors.
