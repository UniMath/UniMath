(*****************************************************************************************

 The double bicategory of squares

 In this file, we define the double bicategory of squares for a given bicategory `B`. This
 double bicategory is defined as follows:
 - Objects: objects in `B`
 - Vertical 1-cells: 1-cells in `B`
 - Horizontal 1-cells: 1-cells in `B`
 - Vertical 2-cells: 2-cells in `B^co`
 - Horizontal 2-cells: 2-cells in `B`
 - Squares: 2-cells in a certain square
 Note that compared to Verity, the role of the vertical and horizontal 2-cells is reversed.
 In Verity's definition, horizontal 2-cells are 2-cells in `B^co` and vertical 2-cells are
 2-cells in `B` (page 96 in "Enriched Categories, Internal Categories and Change of Base").
 However, since the definition of double bicategory is symmetric, this difference is not
 very relevant. The reason for swapping the role between the horizontal and vertical 2-cells,
 is so that we can take `B` as the horizontal bicategory. We also show that the horizontal
 and vertical 2-cells in this double bicategory are the same as certain squares.

 References
 - Enriched Categories, Internal Categories and Change of Base
   Dominic Verity
   ([http://www.tac.mta.ca/tac/reprints/articles/20/tr20.pdf])

 Contents
 1. The data of the double bicategory of squares
 2. The laws
 3. The double bicategory of squares
 4. 2-cells coincide with certain squares

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.

Local Open Scope cat.

Section SquareDoubleBicat.
  Context (B : bicat).

  (** * 1. The data of the double bicategory of squares *)
  Definition square_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor B B.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, x --> y).
    - exact (λ x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂, h₁ · v₂ ==> v₁ · h₂).
  Defined.

  Definition square_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp square_twosided_disp_cat_ob_mor.
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

  Definition square_twosided_disp_cat_data
    : twosided_disp_cat_data B B.
  Proof.
    simple refine (_ ,, _).
    - exact square_twosided_disp_cat_ob_mor.
    - exact square_twosided_disp_cat_id_comp.
  Defined.

  Definition square_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact B.
    - exact square_twosided_disp_cat_data.
  Defined.

  Definition square_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp square_ver_sq_bicat.
  Proof.
    split.
    - split.
      + exact (λ x, id₁ x).
      + exact (λ _ _ _ f g, f · g).
    - exact (λ x y v₁ v₂, v₂ ==> v₁).
  Defined.

  Definition square_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells square_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - exact (λ _ _ f, id2 f).
    - exact (λ _ _ f, linvunitor f).
    - exact (λ _ _ f, rinvunitor f).
    - exact (λ _ _ f, lunitor f).
    - exact (λ _ _ f, runitor f).
    - exact (λ _ _ _ _ f g h, lassociator f g h).
    - exact (λ _ _ _ _ f g h, rassociator f g h).
    - exact (λ _ _ _ _ _ τ θ, θ • τ).
    - exact (λ _ _ _ f _ _ τ, f ◃ τ).
    - exact (λ _ _ _ _ _  g τ, τ ▹ g).
  Defined.

  Proposition square_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws square_ver_sq_bicat_id_comp_cells.
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

  Definition square_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact square_ver_sq_bicat.
    - exact square_ver_sq_bicat_ver_id_comp.
    - exact square_ver_sq_bicat_id_comp_cells.
    - exact square_ver_sq_bicat_prebicat_laws.
    - abstract
        (intros x y f g ;
         apply cellset_property).
  Defined.

  Definition square_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq square_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ x y v, runitor _ • linvunitor _).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ v₁ v₂ w₁ w₂ τ θ, _) ; cbn in *.
      exact (lassociator _ _ _
             • (τ ▹ _)
             • rassociator _ _ _
             • (_ ◃ θ)
             • lassociator _ _ _).
  Defined.

  Definition square_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact square_ver_bicat_sq_bicat.
    - exact square_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  Definition square_double_bicat_whiskering
    : double_bicat_whiskering square_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split ; cbn.
    - exact (λ w x y z h₁ h₂ v₁ v₁' v₂ τ θ, θ • (τ ▹ _)).
    - exact (λ w x y z h₁ h₂ v₁ v₂ v₂' τ θ, (_ ◃ τ) • θ).
    - exact (λ w x y z h₁ h₁' h₂ v₁ v₂ τ θ, (τ ▹ _) • θ).
    - exact (λ w x y z h₁ h₂ h₂' v₁ v₂ τ θ, θ • (_ ◃ τ)).
  Defined.

  Definition square_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact square_ver_bicat_sq_bicat_ver_id_comp.
    - exact square_double_bicat_whiskering.
  Defined.

  (** * 2. The laws *)
  Proposition square_whisker_square_bicat_law
    : whisker_square_bicat_law square_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; cbn ; intros.
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

  Proposition square_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws square_ver_bicat_sq_id_comp_whisker.
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

  Proposition square_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws square_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split ; cbn.
    - intros.
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
    - intros.
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
    - intros.
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
    - intros.
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
    - intros.
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
    - intros.
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

  Proposition square_double_bicat_laws
    : double_bicat_laws square_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact square_whisker_square_bicat_law.
    - exact square_double_bicat_id_comp_square_laws.
    - exact square_double_bicat_cylinder_laws.
    - intro ; intros.
      apply cellset_property.
  Qed.

  (** * 3. The double bicategory of squares *)
  Definition square_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact square_ver_bicat_sq_id_comp_whisker.
    - exact square_double_bicat_laws.
  Defined.

  (** * 4. 2-cells coincide with certain squares *)
  Definition square_vertical_cells_are_squares
    : vertical_cells_are_squares square_verity_double_bicat.
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

  Definition square_horizontal_cells_are_squares
    : horizontal_cells_are_squares square_verity_double_bicat.
  Proof.
    intros x y h₁ h₂.
    use isweq_iso.
    - exact (λ τ, rinvunitor _ • τ • lunitor _).
    - abstract
        (intros τ ; cbn ;
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
End SquareDoubleBicat.
