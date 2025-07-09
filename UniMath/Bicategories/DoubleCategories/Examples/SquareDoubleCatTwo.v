(******************************************************************************************

 The square double category of a 2-category

 In this file, we construct the square double category of a 2-category. Given a 2-category
 `C`, we define the following double category:
 - Objects: objects in `C`
 - Vertical morphisms: morphisms in `C`
 - Horizontal morphisms: morphisms in `C`
 - Squares with vertical sides `f : x₁ --> x₂` and `g : y₁ --> y₂` and horizontal sides
   `h : x₁ --> y₁` and `k : x₂ --> y₂` are 2-cells `h · g ==> f · k`

 One interesting aspect of this double category is its univalence. To guarantee that this
 double category is univalent, we need to assume that `C` is both univalent (which gives
 the univalence of the vertical category) and locally univalent (which gives the univalence
 of the horizontal category). This is because to guarantee that the horizontal category
 is univalent, identity of horizontal morphisms must correspond to invertible squares. This
 is not necessarily the case if `C` is only univalent as a category. If `C` is a category
 enriched in posets, then it satisfies this local univalence condition, and we thus obtain
 a univalent double category.

 Contents
 1. Horizontal operations
 2. The square double category of a 2-category
 3. The square pseudo double setcategory of a 2-setcategory

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Import TwoCategories.Notations.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.SquaresTwoCat.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.

Section ArrowDoubleCategory.
  Context (C : two_cat).

  (** The following notation makes the goals more readable *)
  Local Notation "'idto2mor'" := (idto2mor _) (only printing).

  (** * 1. Horizontal operations *)
  Definition hor_id_data_two_cat_arrow_twosided_disp_cat
    : hor_id_data (two_cat_arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id_data ; cbn.
    - exact (λ x, identity x).
    - exact (λ x y f, two_cat_lunitor _ • two_cat_rinvunitor _).
  Defined.

  Proposition hor_id_laws_two_cat_arrow_twosided_disp_cat
    : hor_id_laws hor_id_data_two_cat_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - cbn.
      unfold two_cat_lunitor, two_cat_runitor, two_cat_linvunitor, two_cat_rinvunitor.
      rewrite !idto2mor_comp.
      apply maponpaths.
      apply (homset_property C).
    - cbn.
      unfold two_cat_lunitor, two_cat_rinvunitor, two_cat_linvunitor.
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !idto2mor_comp.
      apply maponpaths.
      apply (homset_property C).
  Qed.

  Definition hor_id_two_cat_arrow_twosided_disp_cat
    : hor_id (two_cat_arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id.
    - exact hor_id_data_two_cat_arrow_twosided_disp_cat.
    - exact hor_id_laws_two_cat_arrow_twosided_disp_cat.
  Defined.

  Definition hor_comp_data_two_cat_arrow_twosided_disp_cat
    : hor_comp_data (two_cat_arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f · g).
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn in *.
      exact (two_cat_rassociator _ _ _
             • (_ ◃ s₂)
             • two_cat_lassociator _ _ _
             • (s₁ ▹ _)
             • two_cat_rassociator _ _ _).
  Defined.

  Definition hor_comp_laws_two_cat_arrow_twosided_disp_cat
    : hor_comp_laws hor_comp_data_two_cat_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - cbn in *.
      unfold two_cat_runitor, two_cat_linvunitor.
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !idto2mor_comp.
      apply maponpaths.
      apply (homset_property C).
    - cbn in *.
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      rewrite !idto2mor_lwhisker.
      rewrite !idto2mor_rwhisker.
      rewrite !vassocr.
      rewrite !idto2mor_comp.
      rewrite !vassocl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply rwhisker_lwhisker_mor.
        }
        unfold two_cat_lassociator, two_cat_rassociator.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite idto2mor_comp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply lwhisker_rwhisker_mor.
        }
        unfold two_cat_lassociator, two_cat_rassociator.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply lwhisker_lwhisker_mor.
        }
        unfold two_cat_lassociator, two_cat_rassociator.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite !idto2mor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply rwhisker_rwhisker_mor.
          }
          unfold two_cat_lassociator, two_cat_rassociator.
          rewrite !vassocr.
          rewrite !idto2mor_comp.
          rewrite !vassocl.
          rewrite !idto2mor_comp.
          apply idpath.
        }
        rewrite idto2mor_id.
        rewrite id2_left.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          refine (!_).
          apply vcomp_whisker.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply rwhisker_comp_mor.
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply lwhisker_comp_mor.
          }
          unfold two_cat_lassociator, two_cat_rassociator.
          rewrite !vassocl.
          rewrite idto2mor_comp.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite idto2mor_comp.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite idto2mor_comp.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite !idto2mor_comp.
        rewrite !vassocl.
        rewrite !idto2mor_comp.
        apply idpath.
      }
      rewrite !vassocr.
      use idto2mor_right.
      apply maponpaths_2.
      use idto2mor_right.
      apply maponpaths_2.
      use idto2mor_right.
      apply maponpaths_2.
      use idto2mor_right.
      apply maponpaths_2.
      apply maponpaths.
      apply (homset_property C).
  Qed.

  Definition hor_comp_two_cat_arrow_twosided_disp_cat
    : hor_comp (two_cat_arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp.
    - exact hor_comp_data_two_cat_arrow_twosided_disp_cat.
    - exact hor_comp_laws_two_cat_arrow_twosided_disp_cat.
  Defined.

  Definition double_cat_lunitor_two_cat_arrow_twosided_disp_cat_data
    : double_lunitor_data
        hor_id_two_cat_arrow_twosided_disp_cat
        hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    intros x y f ; cbn.
    use z_iso_to_iso_two_cat_arrow.
    use make_z_iso.
    - apply two_cat_lunitor.
    - apply two_cat_linvunitor.
    - abstract
        (split ; [ apply two_cat_lunitor_linvunitor | ] ;
         apply two_cat_linvunitor_lunitor).
  Defined.

  Proposition double_cat_lunitor_two_cat_arrow_twosided_disp_cat_laws
    : double_lunitor_laws
        double_cat_lunitor_two_cat_arrow_twosided_disp_cat_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_two_cat_arrow.
    unfold two_cat_lassociator, two_cat_rassociator.
    unfold two_cat_lunitor, two_cat_linvunitor.
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_rwhisker.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply id1_lwhisker.
    }
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply rwhisker_id1.
    }
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply id1_lwhisker.
    }
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    use arr_idto2mor_eq.
    apply idpath.
  Qed.

  Definition double_cat_lunitor_two_cat_arrow_twosided_disp_cat
    : double_cat_lunitor
        hor_id_two_cat_arrow_twosided_disp_cat
        hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    use make_double_lunitor.
    - exact double_cat_lunitor_two_cat_arrow_twosided_disp_cat_data.
    - exact double_cat_lunitor_two_cat_arrow_twosided_disp_cat_laws.
  Defined.

  Definition double_cat_runitor_two_cat_arrow_twosided_disp_cat_data
    : double_runitor_data
        hor_id_two_cat_arrow_twosided_disp_cat
        hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    intros x y f ; cbn.
    use z_iso_to_iso_two_cat_arrow.
    use make_z_iso.
    - apply two_cat_runitor.
    - apply two_cat_rinvunitor.
    - abstract
        (split ; [ apply two_cat_runitor_rinvunitor | ] ;
         apply two_cat_rinvunitor_runitor).
  Defined.

  Proposition double_cat_runitor_two_cat_arrow_twosided_disp_cat_laws
    : double_runitor_laws
        double_cat_runitor_two_cat_arrow_twosided_disp_cat_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_two_cat_arrow.
    unfold two_cat_lassociator, two_cat_rassociator.
    unfold two_cat_lunitor, two_cat_linvunitor.
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_rwhisker.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply id1_lwhisker.
    }
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply rwhisker_id1.
    }
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply rwhisker_id1.
    }
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite !vassocl.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    use arr_idto2mor_eq.
    apply idpath.
  Qed.

  Definition double_cat_runitor_two_cat_arrow_twosided_disp_cat
    : double_cat_runitor
        hor_id_two_cat_arrow_twosided_disp_cat
        hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    use make_double_runitor.
    - exact double_cat_runitor_two_cat_arrow_twosided_disp_cat_data.
    - exact double_cat_runitor_two_cat_arrow_twosided_disp_cat_laws.
  Defined.

  Definition double_cat_associator_two_cat_arrow_twosided_disp_cat_data
    : double_associator_data hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    intros w x y z h₁ h₂ h₃ ; cbn.
    use z_iso_to_iso_two_cat_arrow.
    use make_z_iso.
    - apply two_cat_lassociator.
    - apply two_cat_rassociator.
    - abstract
        (split ; [ apply two_cat_lassociator_rassociator | ] ;
         apply two_cat_rassociator_lassociator).
  Defined.

  Proposition double_cat_associator_two_cat_arrow_twosided_disp_cat_laws
    : double_associator_laws
        double_cat_associator_two_cat_arrow_twosided_disp_cat_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_disp_mor2_two_cat_arrow.
    unfold two_cat_lassociator, two_cat_rassociator.
    unfold two_cat_lunitor, two_cat_linvunitor.
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_rwhisker.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_comp.
    rewrite !vassocr.
    rewrite !idto2mor_comp.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply id1_lwhisker.
      }
      unfold two_cat_lunitor, two_cat_linvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply rwhisker_rwhisker_mor.
      }
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply id1_lwhisker.
      }
      unfold two_cat_lunitor, two_cat_linvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply lwhisker_rwhisker_mor.
      }
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply id1_lwhisker.
      }
      unfold two_cat_lunitor, two_cat_linvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply lwhisker_comp_mor.
      }
      unfold two_cat_lassociator, two_cat_rassociator.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply rwhisker_id1.
      }
      unfold two_cat_runitor, two_cat_rinvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply rwhisker_id1.
      }
      unfold two_cat_runitor, two_cat_rinvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite !idto2mor_comp.
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply rwhisker_id1.
      }
      unfold two_cat_runitor, two_cat_rinvunitor.
      rewrite !vassocl.
      rewrite idto2mor_comp.
      rewrite !vassocr.
      rewrite idto2mor_comp.
      apply idpath.
    }
    refine (arr_idto2mor_eq3 _ _ _ _ _ _ _ _ _ _ _) ; apply idpath.
  Qed.

  Definition double_cat_associator_two_cat_arrow_twosided_disp_cat
    : double_cat_associator hor_comp_two_cat_arrow_twosided_disp_cat.
  Proof.
    use make_double_associator.
    - exact double_cat_associator_two_cat_arrow_twosided_disp_cat_data.
    - exact double_cat_associator_two_cat_arrow_twosided_disp_cat_laws.
  Defined.

  Proposition triangle_law_two_cat_arrow_twosided_disp_cat
    : triangle_law
        double_cat_lunitor_two_cat_arrow_twosided_disp_cat
        double_cat_runitor_two_cat_arrow_twosided_disp_cat
        double_cat_associator_two_cat_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    cbn.
    rewrite transportb_disp_mor2_two_cat_arrow.
    unfold two_cat_lassociator, two_cat_rassociator.
    unfold two_cat_runitor, two_cat_rinvunitor.
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_rwhisker.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_comp.
    apply maponpaths.
    apply (homset_property C).
  Qed.

  Proposition pentagon_law_two_cat_arrow_twosided_disp_cat
    : pentagon_law double_cat_associator_two_cat_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    cbn.
    rewrite transportb_disp_mor2_two_cat_arrow.
    unfold two_cat_lassociator, two_cat_rassociator.
    unfold two_cat_runitor, two_cat_rinvunitor.
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_rwhisker.
    rewrite !idto2mor_lwhisker.
    rewrite !idto2mor_comp.
    apply maponpaths.
    apply (homset_property C).
  Qed.
End ArrowDoubleCategory.

(** * 2. The square double category of a 2-category *)
Definition two_cat_square_double_cat
           (C : two_cat)
  : double_cat.
Proof.
  use make_double_cat.
  - exact C.
  - exact (two_cat_arrow_twosided_disp_cat C).
  - exact (hor_id_two_cat_arrow_twosided_disp_cat C).
  - exact (hor_comp_two_cat_arrow_twosided_disp_cat C).
  - exact (double_cat_lunitor_two_cat_arrow_twosided_disp_cat C).
  - exact (double_cat_runitor_two_cat_arrow_twosided_disp_cat C).
  - exact (double_cat_associator_two_cat_arrow_twosided_disp_cat C).
  - exact (triangle_law_two_cat_arrow_twosided_disp_cat C).
  - exact (pentagon_law_two_cat_arrow_twosided_disp_cat C).
Defined.

Definition all_companions_two_cat_square_double_cat
           (C : two_cat)
  : all_companions_double_cat (two_cat_square_double_cat C).
Proof.
  intros x y f.
  refine (f ,, _).
  use make_double_cat_are_companions'.
  - apply id2.
  - apply id2.
  - abstract
      (cbn ;
       rewrite id2_rwhisker ;
       rewrite lwhisker_id2 ;
       rewrite !id2_right ;
       rewrite <- !lwhisker_vcomp ;
       rewrite <- !rwhisker_vcomp ;
       refine (transportf_disp_mor2_two_cat_arrow _ _ _ _ @ _) ;
       unfold two_cat_lassociator, two_cat_rassociator ;
       unfold two_cat_runitor, two_cat_rinvunitor ;
       unfold two_cat_lunitor, two_cat_linvunitor ;
       rewrite !vassocl ;
       rewrite !idto2mor_lwhisker ;
       rewrite !idto2mor_rwhisker ;
       rewrite !idto2mor_comp ;
       apply maponpaths ;
       apply (homset_property C)).
  - abstract
      (cbn ;
       rewrite id2_rwhisker ;
       rewrite lwhisker_id2 ;
       rewrite !id2_right ;
       refine (transportf_disp_mor2_two_cat_arrow _ _ _ _ @ _) ;
       unfold two_cat_lassociator, two_cat_rassociator ;
       unfold two_cat_runitor, two_cat_rinvunitor ;
       unfold two_cat_lunitor, two_cat_linvunitor ;
       rewrite !vassocl ;
       rewrite !idto2mor_lwhisker ;
       rewrite !idto2mor_rwhisker ;
       rewrite !idto2mor_comp ;
       apply maponpaths ;
       apply (homset_property C)).
Defined.

Definition two_cat_square_univalent_double_cat
           (C : univalent_two_cat)
           (H : locally_univalent_two_cat C)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (two_cat_square_double_cat C).
  - split.
    + apply C.
    + apply is_univalent_two_cat_arrow.
      exact H.
Defined.

(** * 3. The square pseudo double setcategory of a 2-setcategory *)
Definition strict_two_cat_square_double_cat
           (C : two_setcat)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (two_cat_square_double_cat C).
  - use is_setcategory_two_setcat.
  - use is_strict_two_cat_arrow_twosided_disp_cat.
Defined.
