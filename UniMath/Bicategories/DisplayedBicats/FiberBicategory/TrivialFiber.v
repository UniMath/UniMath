(*******************************************************************
 Fibers of the trivial displayed bicategory

 In this file, we calculate the fibers of the trivial displayed
 bicategory

 1. To the fiber
 2. From the fiber
 3. The unit
 4. The counit
 5. The modifications
 6. The biequivalence

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.TrivialCleaving.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Section FiberOfTrivial.
  Context (B₁ B₂ : bicat)
          (x : B₁).

  (**
   1. To the fiber
   *)
  Definition to_fiber_trivial_data
    : psfunctor_data
        B₂
        (strict_fiber_bicat
           (trivial_displayed_bicat B₁ B₂)
           (trivial_local_isocleaving B₁ B₂)
           x).
  Proof.
    use make_psfunctor_data.
    - exact (λ z, z).
    - exact (λ _ _ f, f).
    - exact (λ _ _ _ _ α, α).
    - exact (λ _, id2 _).
    - exact (λ _ _ _ _ _, id2 _).
  Defined.

  Definition to_fiber_trivial_laws
    : psfunctor_laws to_fiber_trivial_data.
  Proof.
    repeat split ; intro ; intros ; cbn ; rewrite !transportf_const ; cbn.
    - apply idpath.
    - rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite !lwhisker_id2, !id2_rwhisker, !id2_left, !id2_right.
      apply idpath.
    - rewrite !id2_left, !id2_right.
      apply idpath.
    - rewrite !id2_left, !id2_right.
      apply idpath.
  Qed.

  Definition to_fiber_invertible_cells
    : invertible_cells to_fiber_trivial_data.
  Proof.
    split ; intros.
    - apply is_invertible_2cell_id₂.
    - apply is_invertible_2cell_id₂.
  Defined.

  Definition to_fiber_trivial
    : psfunctor
        B₂
        (strict_fiber_bicat
           (trivial_displayed_bicat B₁ B₂)
           (trivial_local_isocleaving B₁ B₂)
           x).
  Proof.
    use make_psfunctor.
    - exact to_fiber_trivial_data.
    - exact to_fiber_trivial_laws.
    - exact to_fiber_invertible_cells.
  Defined.

  (**
   2. From the fiber
   *)
  Definition from_fiber_trivial_data
    : psfunctor_data
        (strict_fiber_bicat
           (trivial_displayed_bicat B₁ B₂)
           (trivial_local_isocleaving B₁ B₂)
           x)
        B₂.
  Proof.
    use make_psfunctor_data.
    - exact (λ z, z).
    - exact (λ _ _ f, f).
    - exact (λ _ _ _ _ α, α).
    - exact (λ _, id2 _).
    - exact (λ a b c f g, id2 _).
  Defined.

  Definition from_fiber_trivial_data_laws
    : psfunctor_laws from_fiber_trivial_data.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _) ;
    intro ; intros ;
    cbn ;
    try (rewrite !transportf_const).
    - apply idpath.
    - apply idpath.
    - rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite !lwhisker_id2, !id2_rwhisker, !id2_left, !id2_right.
      apply idpath.
    - rewrite !id2_left, !id2_right.
      apply idpath.
    - rewrite !id2_left, !id2_right.
      apply idpath.
  Qed.

  Definition from_fiber_trivial
    : psfunctor
        (strict_fiber_bicat
           (trivial_displayed_bicat B₁ B₂)
           (trivial_local_isocleaving B₁ B₂)
           x)
        B₂.
  Proof.
    use make_psfunctor.
    - exact from_fiber_trivial_data.
    - exact from_fiber_trivial_data_laws.
    - split ; cbn ; intros ; is_iso.
  Defined.

  (**
   3. The unit
   *)
  Definition fiber_trivial_unit_data
    : pstrans_data
        (id_psfunctor _)
        (comp_psfunctor from_fiber_trivial to_fiber_trivial).
  Proof.
    use make_pstrans_data ; cbn.
    - exact (λ _, id₁ _).
    - exact (λ x y f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition fiber_trivial_unit_is_pstrans
    : is_pstrans fiber_trivial_unit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - cbn.
      intros y₁ y₂ f g α.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - cbn.
      intro y.
      rewrite !id2_left.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - cbn.
      intros y₁ y₂ y₃ f g.
      rewrite !id2_left.
      rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lwhisker_vcomp.
      refine (!(id2_left _) @_).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition fiber_trivial_unit
    : pstrans
        (id_psfunctor _)
        (comp_psfunctor from_fiber_trivial to_fiber_trivial).
  Proof.
    use make_pstrans.
    - exact fiber_trivial_unit_data.
    - exact fiber_trivial_unit_is_pstrans.
  Defined.

  Definition fiber_trivial_unit_inv_data
    : pstrans_data
        (comp_psfunctor from_fiber_trivial to_fiber_trivial)
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - exact (λ x, id₁ _).
    - exact (λ x y f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition fiber_trivial_unit_inv_is_pstrans
    : is_pstrans fiber_trivial_unit_inv_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros y₁ y₂ f g α ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - intros y ; cbn.
      rewrite id2_left.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros y₁ y₂ y₃ f g ; cbn.
      rewrite id2_left.
      rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lwhisker_vcomp.
      refine (!(id2_left _) @_).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition fiber_trivial_unit_inv
    : pstrans
        (comp_psfunctor from_fiber_trivial to_fiber_trivial)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact fiber_trivial_unit_inv_data.
    - exact fiber_trivial_unit_inv_is_pstrans.
  Defined.

  (**
   4. The counit
   *)
  Definition fiber_trivial_counit_data
    : pstrans_data
        (comp_psfunctor to_fiber_trivial from_fiber_trivial)
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - cbn.
      exact (λ _, id₁ _).
    - simple refine (λ x y f, make_invertible_2cell _).
      + cbn.
        exact (lunitor _ • rinvunitor _).
      + use strict_fiber_bicat_invertible_2cell.
        apply trivial_is_invertible_2cell_to_is_disp_invertible ; cbn.
        is_iso.
  Defined.

  Definition fiber_trivial_counit_is_pstrans
    : is_pstrans fiber_trivial_counit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros y₁ y₂ f g α ; cbn.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - cbn.
      intro y.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - cbn.
      intros y₁ y₂ y₃ f g.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lwhisker_vcomp.
      refine (!(id2_left _) @_).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition fiber_trivial_counit
    : pstrans
        (comp_psfunctor to_fiber_trivial from_fiber_trivial)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact fiber_trivial_counit_data.
    - exact fiber_trivial_counit_is_pstrans.
  Defined.

  Definition fiber_trivial_counit_inv_data
    : pstrans_data
        (id_psfunctor _)
        (comp_psfunctor to_fiber_trivial from_fiber_trivial).
  Proof.
    use make_pstrans_data.
    - cbn.
      exact (λ z, id₁ _).
    - simple refine (λ x y f, make_invertible_2cell _).
      + cbn.
        exact (lunitor _ • rinvunitor _).
      + use strict_fiber_bicat_invertible_2cell.
        apply trivial_is_invertible_2cell_to_is_disp_invertible ; cbn.
        is_iso.
  Defined.

  Definition fiber_trivial_counit_inv_is_pstrans
    : is_pstrans fiber_trivial_counit_inv_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros y₁ y₂ f g α ; cbn.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    - intros y ; cbn.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros y₁ y₂ y₃ f g ; cbn.
      rewrite !transportf_const ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lwhisker_vcomp.
      refine (!(id2_left _) @_).
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition fiber_trivial_counit_inv
    : pstrans
        (id_psfunctor _)
        (comp_psfunctor to_fiber_trivial from_fiber_trivial).
  Proof.
    use make_pstrans.
    - exact fiber_trivial_counit_inv_data.
    - exact fiber_trivial_counit_inv_is_pstrans.
  Defined.

  (**
   5. The modifications
   *)
  Definition trivial_unit_inv_left_data
    : invertible_modification_data
        (id_pstrans _)
        (comp_pstrans fiber_trivial_unit_inv fiber_trivial_unit).
  Proof.
    intros y.
    use make_invertible_2cell ; cbn.
    - exact (rinvunitor (id₁ y)).
    - is_iso.
  Defined.

  Definition trivial_unit_inv_left_is_modification
    : is_modification trivial_unit_inv_left_data.
  Proof.
    intros y₁ y₂ f.
    cbn.
    rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite <- vcomp_lunitor.
    rewrite <- lunitor_triangle.
    rewrite !vassocl.
    do 3 apply maponpaths.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite lunitor_V_id_is_left_unit_V_id.
    apply idpath.
  Qed.

  Definition trivial_unit_inv_left
    : invertible_modification
        (id_pstrans _)
        (comp_pstrans fiber_trivial_unit_inv fiber_trivial_unit).
  Proof.
    use make_invertible_modification.
    - exact trivial_unit_inv_left_data.
    - exact trivial_unit_inv_left_is_modification.
  Defined.

  Definition trivial_unit_inv_right_data
    : invertible_modification_data
        (comp_pstrans fiber_trivial_unit fiber_trivial_unit_inv)
        (id_pstrans _).
  Proof.
    intros y.
    use make_invertible_2cell ; cbn.
    - exact (runitor _).
    - is_iso.
  Defined.

  Definition trivial_unit_inv_right_is_modification
    : is_modification trivial_unit_inv_right_data.
  Proof.
    intros y₁ y₂ f ; cbn.
    cbn.
    rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- vcomp_lunitor.
    apply maponpaths.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite !vassocl.
    refine (_ @ id2_right _).
    apply maponpaths.
    rewrite runitor_lunitor_identity.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    apply id2_rwhisker.
  Qed.

  Definition trivial_unit_inv_right
    : invertible_modification
        (comp_pstrans fiber_trivial_unit fiber_trivial_unit_inv)
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact trivial_unit_inv_right_data.
    - exact trivial_unit_inv_right_is_modification.
  Defined.

  Definition trivial_counit_inv_right_data
    : invertible_modification_data
        (id_pstrans _)
        (comp_pstrans fiber_trivial_counit fiber_trivial_counit_inv).
  Proof.
    intros y.
    use make_invertible_2cell ; cbn.
    - exact (rinvunitor _).
    - use strict_fiber_bicat_invertible_2cell.
      apply trivial_is_invertible_2cell_to_is_disp_invertible ; cbn.
      is_iso.
  Defined.

  Definition trivial_counit_inv_right_is_modification
    : is_modification trivial_counit_inv_right_data.
  Proof.
    intros y₁ y₂ f ; cbn.
    rewrite !transportf_const ; cbn.
    rewrite !id2_left, !id2_right.
    rewrite !id2_rwhisker, !lwhisker_id2.
    rewrite !id2_left, !id2_right.
    rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite <- vcomp_lunitor.
    rewrite <- lunitor_triangle.
    rewrite !vassocl.
    do 3 apply maponpaths.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite lunitor_V_id_is_left_unit_V_id.
    apply idpath.
  Qed.

  Definition trivial_counit_inv_right
    : invertible_modification
        (id_pstrans _)
        (comp_pstrans fiber_trivial_counit fiber_trivial_counit_inv).
  Proof.
    use make_invertible_modification.
    - exact trivial_counit_inv_right_data.
    - exact trivial_counit_inv_right_is_modification.
  Defined.

  Definition trivial_counit_inv_left_data
    : invertible_modification_data
        (comp_pstrans fiber_trivial_counit_inv fiber_trivial_counit)
        (id_pstrans _).
  Proof.
    intros y.
    use make_invertible_2cell ; cbn.
    - exact (runitor _).
    - use strict_fiber_bicat_invertible_2cell.
      apply trivial_is_invertible_2cell_to_is_disp_invertible ; cbn.
      is_iso.
  Defined.

  Definition trivial_counit_inv_left_is_modification
    : is_modification trivial_counit_inv_left_data.
  Proof.
    intros y₁ y₂ f ; cbn.
    rewrite !transportf_const ; cbn.
    rewrite !id2_left, !id2_right.
    rewrite !id2_rwhisker, !lwhisker_id2.
    rewrite !id2_left, !id2_right.
    rewrite <- lwhisker_vcomp, <- rwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- vcomp_lunitor.
    apply maponpaths.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite !vassocl.
    refine (_ @ id2_right _).
    apply maponpaths.
    rewrite runitor_lunitor_identity.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    apply id2_rwhisker.
  Qed.

  Definition trivial_counit_inv_left
    : invertible_modification
        (comp_pstrans fiber_trivial_counit_inv fiber_trivial_counit)
        (id_pstrans _).
  Proof.
    use make_invertible_modification.
    - exact trivial_counit_inv_left_data.
    - exact trivial_counit_inv_left_is_modification.
  Defined.

  (**
   6. The biequivalence
   *)
  Definition to_fiber_trivial_is_biequivalence
    : is_biequivalence to_fiber_trivial.
  Proof.
    use make_is_biequivalence.
    - exact from_fiber_trivial.
    - exact fiber_trivial_unit.
    - exact fiber_trivial_unit_inv.
    - exact fiber_trivial_counit.
    - exact fiber_trivial_counit_inv.
    - exact trivial_unit_inv_left.
    - exact trivial_unit_inv_right.
    - exact trivial_counit_inv_right.
    - exact trivial_counit_inv_left.
  Defined.
End FiberOfTrivial.
