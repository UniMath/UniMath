(*****************************************************************************************

 The Verity double bicategory of mates

 In this file, we define the Verity double bicategory of mates for a given bicategory `B`.
 This double bicategory is defined as follows:
 - Objects: objects in `B`
 - Vertical 1-cells: 1-cells in `B`
 - Horizontal 1-cells: left adjoints in `B`
 - Vertical 2-cells: 2-cells in `B^co`
 - Horizontal 2-cells: 2-cells in `B`
 - Squares with vertical sides `v₁ : x₁ --> y₁` and `v₂ : x₂ --> y₂` and horizontal sides
   `l₁ : x₁ --> x₂` and `l₂ : y₁ --> y₂` are `l₁ · v₂ ==> v₁ · l₂`.
 The interesting feature of this bicategory is the role it plays in the mate calculus. We
 could represent the squares of this double bicategory either in the above way or we could
 express the 2-cells using the right adjoints. These two presentations result in equivalent
 double bicategories, which is the core theorem of the mate calculus.

 Contents
 1. The bicategory of left adjoints
 2. The data of the double bicategory of mates
 3. The laws
 4. The double bicategory of mates
 5. 2-cells coincide with certain mates
 6. Companion pairs
 7. Vertical invertible 2-cells
 8. The local univalence of the Verity double bicategory of mates
 9. Vertical adjoint equivalences
 10. The global univalence of the Verity double bicategory of mates

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.Composition.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.Core.

Local Open Scope cat.

(** * 1. The bicategory of left adjoints *)
Definition left_adj_disp_bicat
           (B : bicat)
  : disp_bicat B.
Proof.
  use disp_sub1cell_bicat.
  - exact (λ _ _ f, left_adjoint f).
  - exact (λ x, internal_adjoint_equivalence_identity x).
  - exact (λ _ _ _ f g Hf Hg, comp_left_adjoint f g Hf Hg).
Defined.

Proposition disp_univalent_2_1_left_adj
            {B : bicat}
            (HB : is_univalent_2_1 B)
  : disp_univalent_2_1 (left_adj_disp_bicat B).
Proof.
  use disp_sub1cell_univalent_2_1.
  intros.
  apply isaprop_left_adjoint.
  exact HB.
Qed.

Proposition disp_univalent_2_0_left_adj
            {B : bicat}
            (HB : is_univalent_2_1 B)
  : disp_univalent_2_0 (left_adj_disp_bicat B).
Proof.
  use disp_sub1cell_univalent_2_0.
  - exact HB.
  - intros.
    apply isaprop_left_adjoint.
    exact HB.
Qed.

Proposition disp_univalent_2_left_adj
            {B : bicat}
            (HB : is_univalent_2_1 B)
  : disp_univalent_2 (left_adj_disp_bicat B).
Proof.
  split.
  - exact (disp_univalent_2_0_left_adj HB).
  - exact (disp_univalent_2_1_left_adj HB).
Qed.

Definition left_adj_bicat
           (B : bicat)
  : bicat
  := total_bicat (left_adj_disp_bicat B).

Proposition is_univalent_2_1_left_adj_bicat
            {B : bicat}
            (HB : is_univalent_2_1 B)
  : is_univalent_2_1 (left_adj_bicat B).
Proof.
  use total_is_univalent_2_1.
  - exact HB.
  - exact (disp_univalent_2_1_left_adj HB).
Qed.

Proposition is_univalent_2_0_left_adj_bicat
            {B : bicat}
            (HB : is_univalent_2 B)
  : is_univalent_2_0 (left_adj_bicat B).
Proof.
  use total_is_univalent_2_0.
  - exact (pr1 HB).
  - exact (disp_univalent_2_0_left_adj (pr2 HB)).
Qed.

Proposition is_univalent_2_left_adj_bicat
            {B : bicat}
            (HB : is_univalent_2 B)
  : is_univalent_2 (left_adj_bicat B).
Proof.
  split.
  - exact (is_univalent_2_0_left_adj_bicat HB).
  - exact (is_univalent_2_1_left_adj_bicat (pr2 HB)).
Qed.

Section MateDoubleBicat.
  Context (B : bicat).

  Let LB : bicat := left_adj_bicat B.

  (** * 2. The data of the double bicategory of mates *)
  Definition mate_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor LB LB.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, B ⟦ pr1 x , pr1 y ⟧).
    - cbn.
      exact (λ x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂, pr1 h₁ · v₂ ==> v₁ · pr1 h₂).
  Defined.

  Definition mate_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp mate_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x y f, lunitor _ • rinvunitor _).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ v₃ h₁ h₂ k₁ k₂ τ θ,
             rassociator _ _ _
             • (_ ◃ θ)
             • lassociator _ _ _
             • (τ ▹ _)
             • rassociator _ _ _).
  Defined.

  Definition mate_twosided_disp_cat_data
    : twosided_disp_cat_data LB LB.
  Proof.
    simple refine (_ ,, _).
    - exact mate_twosided_disp_cat_ob_mor.
    - exact mate_twosided_disp_cat_id_comp.
  Defined.

  Definition mate_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact LB.
    - exact mate_twosided_disp_cat_data.
  Defined.

  Definition mate_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp mate_ver_sq_bicat.
  Proof.
    split.
    - split.
      + exact (λ x, id₁ (pr1 x)).
      + exact (λ _ _ _ f g, f · g).
    - exact (λ x y v₁ v₂, v₂ ==> v₁).
  Defined.

  Definition mate_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells mate_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - exact (λ _ _ f, id2 _).
    - exact (λ _ _ f, linvunitor _).
    - exact (λ _ _ f, rinvunitor _).
    - exact (λ _ _ f, lunitor _).
    - exact (λ _ _ f, runitor _).
    - exact (λ _ _ _ _ f g h, lassociator _ _ _).
    - exact (λ _ _ _ _ f g h, rassociator _ _ _).
    - exact (λ _ _ _ _ _ τ θ, θ • τ).
    - exact (λ _ _ _ f _ _ τ, _ ◃ τ).
    - exact (λ _ _ _ _ _  g τ, τ ▹ _).
  Defined.

  Proposition mate_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws mate_ver_sq_bicat_id_comp_cells.
  Proof.
    repeat split ; cbn ; intros.
    - apply id2_right.
    - apply id2_left.
    - apply vassocl.
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      apply idpath.
    - rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      apply idpath.
    - apply lwhisker_lwhisker_rassociator.
    - apply rwhisker_lwhisker_rassociator.
    - apply rwhisker_rwhisker_alt.
    - refine (!_).
      apply vcomp_whisker.
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - rewrite rwhisker_hcomp, lwhisker_hcomp.
      rewrite triangle_r_inv.
      apply idpath.
    - rewrite !vassocr.
      rewrite rassociator_rassociator.
      apply idpath.
  Qed.

  Definition mate_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact mate_ver_sq_bicat.
    - exact mate_ver_sq_bicat_ver_id_comp.
    - exact mate_ver_sq_bicat_id_comp_cells.
    - exact mate_ver_sq_bicat_prebicat_laws.
    - abstract
        (intros x y f g ;
         apply cellset_property).
  Defined.

  Definition mate_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq mate_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ x y v, runitor _ • linvunitor _).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ v₁ v₂ w₁ w₂ τ θ, _).
      exact (lassociator _ _ _
             • (τ ▹ _)
             • rassociator _ _ _
             • (_ ◃ θ)
             • lassociator _ _ _).
  Defined.

  Definition mate_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact mate_ver_bicat_sq_bicat.
    - exact mate_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  Definition mate_double_bicat_whiskering
    : double_bicat_whiskering mate_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - refine (λ w x y z h₁ h₂ v₁ v₁' v₂ τ θ, θ • (τ ▹ _)).
    - exact (λ w x y z h₁ h₂ v₁ v₂ v₂' τ θ, (_ ◃ τ) • θ).
    - exact (λ w x y z h₁ h₁' h₂ v₁ v₂ τ θ, (pr1 τ ▹ _) • θ).
    - exact (λ w x y z h₁ h₂ h₂' v₁ v₂ τ θ, θ • (_ ◃ pr1 τ)).
  Defined.

  Definition mate_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact mate_ver_bicat_sq_bicat_ver_id_comp.
    - exact mate_double_bicat_whiskering.
  Defined.

  (** * 3. The laws *)
  Proposition mate_whisker_square_bicat_law
    : whisker_square_bicat_law mate_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    - rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    - rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    - rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    - rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    - rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
    - rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    - rewrite !vassocl.
      apply idpath.
    - rewrite !vassocl.
      apply idpath.
    - rewrite !vassocr.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite !vassocl.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite !vassocl.
      apply idpath.
    - rewrite !vassocl.
      apply idpath.
    - rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rinvunitor_natural.
      rewrite rwhisker_hcomp.
      apply idpath.
    - rewrite !vassocr.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite linvunitor_natural.
      rewrite lwhisker_hcomp.
      apply idpath.
    - rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply idpath.
    - rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      rewrite <- lwhisker_vcomp.
      apply idpath.
    - apply maponpaths_2.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      apply idpath.
    - rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      apply idpath.
    - rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      apply idpath.
    - apply maponpaths_2.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Proposition mate_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws mate_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; cbn ; intros.
    - rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite <- rassociator_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      apply lassociator_lassociator.
    - rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite <- lunitor_triangle.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      apply id2_rwhisker.
    - rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite <- runitor_triangle.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite linvunitor_assoc.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      apply lwhisker_id2.
  Qed.

  Proposition mate_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws mate_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intros ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rassociator_rassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      refine (!_).
      apply rassociator_rassociator.
    - intros ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      refine (!_).
      apply lassociator_lassociator.
    - intros ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    - intros ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite triangle_l_inv.
        rewrite <- rwhisker_hcomp.
        rewrite rwhisker_vcomp.
        rewrite rinvunitor_runitor.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite <- linvunitor_assoc.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite linvunitor_assoc.
      rewrite !vassocl.
      rewrite rassociator_lassociator.
      apply id2_right.
    - intros ; cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- runitor_triangle.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite lwhisker_id2.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      apply idpath.
    - intros ; cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 5 apply maponpaths.
        rewrite lwhisker_hcomp.
        rewrite triangle_l_inv.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite runitor_triangle.
      rewrite vcomp_runitor.
      refine (_ @ id2_left _).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- runitor_triangle.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite lwhisker_id2.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q.
      cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite <- p.
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        apply idpath.
      }
      clear p.
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- q ; clear q.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_lwhisker.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₁' v₂ v₂'.
      intros w₁ w₁' w₂ w₂' τ₁ τ₂ θ₁ θ₂ s₁ s₁' s₂ s₂' p q.
      cbn in p, q ; cbn.
      unfold hcomp.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite p.
        rewrite <- rwhisker_vcomp.
        apply idpath.
      }
      clear p.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite q.
        rewrite <- lwhisker_vcomp.
        apply idpath.
      }
      clear q.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_lwhisker_rassociator.
      apply idpath.
  Qed.

  Proposition mate_double_bicat_laws
    : double_bicat_laws mate_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact mate_whisker_square_bicat_law.
    - exact mate_double_bicat_id_comp_square_laws.
    - exact mate_double_bicat_cylinder_laws.
    - intro ; intros.
      apply cellset_property.
  Qed.

  (** * 4. The double bicategory of mates *)
  Definition mate_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact mate_ver_bicat_sq_id_comp_whisker.
    - exact mate_double_bicat_laws.
  Defined.

  (** * 5. 2-cells coincide with certain mates *)
  Definition mate_vertically_saturated
    : vertically_saturated mate_verity_double_bicat.
  Proof.
    intros x y v₁ v₂.
    use isweq_iso.
    - exact (λ τ, linvunitor _ • τ • runitor _).
    - abstract
        (intros τ ; cbn ;
         rewrite !vassocr ;
         rewrite linvunitor_lunitor ;
         rewrite id2_left ;
         rewrite !vassocl ;
         rewrite vcomp_runitor ;
         rewrite !vassocr ;
         rewrite rinvunitor_runitor ;
         apply id2_left).
    - abstract
        (intros τ ; cbn ;
         rewrite rwhisker_hcomp ;
         rewrite !vassocl ;
         rewrite <- rinvunitor_natural ;
         rewrite !vassocl ;
         rewrite runitor_rinvunitor ;
         rewrite id2_right ;
         rewrite !vassocr ;
         rewrite lunitor_linvunitor ;
         apply id2_left).
  Defined.

  Definition mate_horizontally_saturated
    : horizontally_saturated mate_verity_double_bicat.
  Proof.
    intros x y h₁ h₂.
    use isweq_iso.
    - exact (λ τ, rinvunitor _ • τ • lunitor _ ,, tt).
    - abstract
        (intros τ ; cbn ;
         use subtypePath ; [ intro ; apply isapropunit | ] ;
         rewrite !vassocl ;
         rewrite linvunitor_lunitor ;
         rewrite id2_right ;
         rewrite vcomp_runitor ;
         rewrite !vassocr ;
         rewrite rinvunitor_runitor ;
         apply id2_left).
    - abstract
        (intros τ ; cbn ;
         rewrite !vassocr ;
         rewrite vcomp_runitor ;
         rewrite !vassocl ;
         rewrite lunitor_linvunitor ;
         rewrite id2_right ;
         rewrite !vassocr ;
         rewrite runitor_rinvunitor ;
         apply id2_left).
  Defined.

  Definition mate_is_weak_double_cat
    : is_weak_double_cat mate_verity_double_bicat.
  Proof.
    split.
    - exact mate_vertically_saturated.
    - exact mate_horizontally_saturated.
  Defined.

  (** * 6. Companion pairs *)
  Definition all_companions_mate_verity_double_bicat
    : all_companions mate_verity_double_bicat.
  Proof.
    intros x y f.
    refine (pr1 f ,, _).
    use make_are_companions ; cbn.
    - apply id2.
    - apply id2.
    - abstract
        (cbn ;
         rewrite id2_rwhisker, lwhisker_id2, !id2_right ;
         rewrite lassociator_rassociator ;
         rewrite id2_left ;
         rewrite lunitor_triangle ;
         rewrite vcomp_lunitor ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite id2_rwhisker, lwhisker_id2, !id2_right ;
         rewrite rassociator_lassociator ;
         rewrite id2_left ;
         rewrite !vassocl ;
         rewrite runitor_triangle ;
         rewrite vcomp_runitor ;
         apply idpath).
  Defined.

  (** * 7. Vertical invertible 2-cells *)
  Definition mate_verity_double_to_ver_inv2cell
             {x y : LB}
             {f g : B ⟦ pr1 x , pr1 y ⟧}
             (τ : invertible_2cell (C := B) f g)
    : invertible_2cell
        (C := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
        f g.
  Proof.
    use make_invertible_2cell.
    - exact (τ^-1).
    - use make_is_invertible_2cell.
      + exact τ.
      + abstract
          (exact (vcomp_rinv τ)).
      + abstract
          (exact (vcomp_linv τ)).
  Defined.

  Definition mate_verity_double_from_ver_inv2cell
             {x y : LB}
             {f g : B ⟦ pr1 x , pr1 y ⟧}
             (τ : invertible_2cell
                    (C := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
                    f g)
    : invertible_2cell (C := B) f g.
  Proof.
    use make_invertible_2cell.
    - exact (τ^-1).
    - use make_is_invertible_2cell.
      + exact τ.
      + abstract
          (exact (vcomp_rinv τ)).
      + abstract
          (exact (vcomp_linv τ)).
  Defined.

  Definition mate_verity_double_ver_inv2cell_weq
             {x y : LB}
             (f g : B ⟦ pr1 x , pr1 y ⟧)
    : invertible_2cell (C := B) f g
      ≃
      invertible_2cell
        (C := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
        f g.
  Proof.
    use weq_iso.
    - exact mate_verity_double_to_ver_inv2cell.
    - exact mate_verity_double_from_ver_inv2cell.
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
    - abstract
        (intro τ ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
  Defined.

  (** * 8. The local univalence of the Verity double bicategory of mates *)
  Definition ver_locally_univalent_mate_verity_double_bicat
             (HB_2_1 : is_univalent_2_1 B)
    : ver_locally_univalent mate_verity_double_bicat.
  Proof.
    intros x y f g.
    use weqhomot.
    - exact (mate_verity_double_ver_inv2cell_weq _ _
             ∘ make_weq _ (HB_2_1 _ _ _ _))%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
         apply idpath).
  Defined.

  Definition locally_univalent_mate_verity_double_bicat
             (HB_2_1 : is_univalent_2_1 B)
    : locally_univalent_verity_double_bicat mate_verity_double_bicat.
  Proof.
    split.
    - use is_univalent_2_1_left_adj_bicat.
      exact HB_2_1.
    - exact (ver_locally_univalent_mate_verity_double_bicat HB_2_1).
  Defined.

  (** * 9. Vertical adjoint equivalences *)
  Definition mate_verity_double_to_ver_adjequiv
             {x y : LB}
             (f : adjoint_equivalence (B := B) (pr1 x) (pr1 y))
    : adjoint_equivalence
        (B := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
        x y.
  Proof.
    use equiv_to_adjequiv.
    - exact f.
    - pose (η := mate_verity_double_to_ver_inv2cell (left_equivalence_unit_iso f)).
      pose (ε := mate_verity_double_to_ver_inv2cell (left_equivalence_counit_iso f)).
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      + exact (left_adjoint_right_adjoint f).
      + exact η.
      + exact ε.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
  Defined.

  Definition mate_verity_double_from_ver_adjequiv
             {x y : LB}
             (f : adjoint_equivalence
                    (B := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
                    x y)
    : adjoint_equivalence (B := B) (pr1 x) (pr1 y).
  Proof.
    use equiv_to_adjequiv.
    - exact f.
    - pose (η := mate_verity_double_from_ver_inv2cell (left_equivalence_unit_iso f)).
      pose (ε := mate_verity_double_from_ver_inv2cell (left_equivalence_counit_iso f)).
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      + exact (left_adjoint_right_adjoint f).
      + exact η.
      + exact ε.
      + apply property_from_invertible_2cell.
      + apply property_from_invertible_2cell.
  Defined.

  Definition mate_verity_double_ver_adjequiv_weq
             (HB_2_1 : is_univalent_2_1 B)
             (x y : LB)
    : adjoint_equivalence (B := B) (pr1 x) (pr1 y)
      ≃
      adjoint_equivalence
        (B := ver_bicat_of_verity_double_bicat mate_verity_double_bicat)
        x y.
  Proof.
    use weq_iso.
    - exact mate_verity_double_to_ver_adjequiv.
    - exact mate_verity_double_from_ver_adjequiv.
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply (isaprop_left_adjoint_equivalence _ HB_2_1) | ] ;
         apply idpath).
    - abstract
        (intros f ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_left_adjoint_equivalence
                    _
                    (ver_locally_univalent_mate_verity_double_bicat HB_2_1))
         | apply idpath ]).
  Defined.

  (** * 10. The global univalence of the Verity double bicategory of mates *)
  Definition ver_globally_univalent_mate_verity_double_bicat
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
    : ver_globally_univalent mate_verity_double_bicat.
  Proof.
    intros x y.
    use weqhomot.
    - refine (mate_verity_double_ver_adjequiv_weq HB_2_1 _ _
              ∘ make_weq _ (HB_2_0 _ _)
              ∘ path_sigma_hprop _ _ _ _)%weq.
      apply isapropunit.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply (isaprop_left_adjoint_equivalence
                 _
                 (ver_locally_univalent_mate_verity_double_bicat HB_2_1)).
      }
      apply idpath.
  Qed.

  Definition globally_univalent_mate_verity_double_bicat
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
    : globally_univalent_verity_double_bicat mate_verity_double_bicat.
  Proof.
    split.
    - use is_univalent_2_0_left_adj_bicat.
      split.
      + exact HB_2_0.
      + exact HB_2_1.
    - exact (ver_globally_univalent_mate_verity_double_bicat HB_2_0 HB_2_1).
  Defined.

  Definition gregarious_univalent_mate_verity_double_bicat
             (HB_2_0 : is_univalent_2_0 B)
             (HB_2_1 : is_univalent_2_1 B)
    : gregarious_univalent mate_verity_double_bicat.
  Proof.
    use hor_globally_univalent_to_gregarious_univalent.
    - exact (locally_univalent_mate_verity_double_bicat HB_2_1).
    - use is_univalent_2_0_left_adj_bicat.
      split.
      + exact HB_2_0.
      + exact HB_2_1.
    - apply mate_vertically_saturated.
  Defined.
End MateDoubleBicat.
