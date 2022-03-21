(**
 Duality involutions of bicategories

 Contents:
 1. Duality involution on locally groupoidal bicategory
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.OtherStructure.DualityInvolution.

Local Open Scope cat.

(**
 1. Duality involution on locally groupoidal bicategory
 *)
Section DualityInvolutionLocallyGroupoidal.
  Context (B : bicat)
          (inv_B : locally_groupoid B).

  Definition op_locally_groupoid_data
    : psfunctor_data (op2_bicat B) B.
  Proof.
    use make_psfunctor_data.
    - exact (λ z, z).
    - exact (λ _ _ f, f).
    - exact (λ _ _ _ _ α, (inv_B _ _ _ _ α)^-1).
    - exact (λ _, id2 _).
    - exact (λ _ _ _ _ _, id2 _).
  Defined.

  Definition op_locally_groupoid_laws
    : psfunctor_laws op_locally_groupoid_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite rassociator_lassociator.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition op_locally_groupoid_invertible_cells
    : invertible_cells op_locally_groupoid_data.
  Proof.
    split ; intro ; intros ; cbn ; is_iso.
  Defined.

  Definition op_locally_groupoid
    : psfunctor (op2_bicat B) B.
  Proof.
    use make_psfunctor.
    - exact op_locally_groupoid_data.
    - exact op_locally_groupoid_laws.
    - exact op_locally_groupoid_invertible_cells.
  Defined.

  Definition locally_groupoid_duality_involution_unit_data
    : pstrans_data
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans_data.
    - exact (λ x, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intro x ; cbn.
      rewrite !id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit
    : pstrans
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_data.
    - exact locally_groupoid_duality_involution_unit_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_data
    : pstrans_data
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans_data.
    - exact (λ _, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_inv_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite vcomp_rinv.
      apply id2_right.
    - intro x ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite lwhisker_id2, !id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit_inv
    : pstrans
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_inv_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_data
    : invertible_modification_data
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    intro x ; cbn.
    exact (linvunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_unit_inv_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    rewrite (rwhisker_hcomp _ (rinvunitor f)).
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite lunitor_V_id_is_left_unit_V_id.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_l_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite !vassocr.
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_unit_inv
    : invertible_modification
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_unit_inv_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_data
    : invertible_modification_data
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    intro x ; cbn.
    exact (lunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_inv_unit_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    rewrite runitor_lunitor_identity.
    apply maponpaths.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_inv_unit
    : invertible_modification
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_inv_unit_data.
    - exact locally_groupoid_duality_involution_unit_inv_unit_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_triangle
             (x : B)
    : invertible_2cell (id₁ x) (id₁ x)
    := id2_invertible_2cell _.

  Definition locally_groupoid_duality_involution_data
    : duality_involution_data op_locally_groupoid
    := make_duality_involution_data
         op_locally_groupoid
         locally_groupoid_duality_involution_unit
         locally_groupoid_duality_involution_unit_inv
         locally_groupoid_duality_involution_unit_unit_inv
         locally_groupoid_duality_involution_unit_inv_unit
         locally_groupoid_duality_involution_triangle.

  Definition locally_groupoid_duality_involution_laws_coh
             (x : B)
    : lunitor (id₁ x)
      • rinvunitor (id₁ x)
      • (id₁ x ◃ id₂ (id₁ x))
      =
      id₁ x ◃ (inv_B x x (id₁ x) (id₁ x) (id₂ (id₁ x)))^-1.
  Proof.
    rewrite lunitor_runitor_identity.
    rewrite runitor_rinvunitor.
    rewrite lwhisker_id2.
    rewrite !id2_left.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite lwhisker_id2.
    apply id2_left.
  Qed.

  Definition locally_groupoid_duality_involution_laws
    : duality_involution_laws locally_groupoid_duality_involution_data.
  Proof.
    split.
    - exact locally_groupoid_duality_involution_laws_coh.
    - intros x y f ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !vassocr.
      rewrite !lunitor_linvunitor.
      rewrite !id2_left.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      refine (!_).
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn.
      rewrite rwhisker_rwhisker_alt.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_hcomp.
          rewrite <- triangle_l.
          rewrite <- lwhisker_hcomp.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- rassociator_rassociator.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite <- lunitor_triangle.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite linvunitor_lunitor.
      rewrite id2_right.
      refine (_ @ id2_right _).
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite lunitor_runitor_identity.
      rewrite lwhisker_vcomp.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2.
      apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution
    : duality_involution op_locally_groupoid
    := locally_groupoid_duality_involution_data
       ,,
       locally_groupoid_duality_involution_laws.
End DualityInvolutionLocallyGroupoidal.
