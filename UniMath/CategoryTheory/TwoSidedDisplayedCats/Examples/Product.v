Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Section ProductTwoSidedDispCat.
  Context (C₁ C₂ : category).

  Definition prod_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, unit).
    - exact (λ _ _ _ _ _ _ _ _, unit).
  Defined.

  Definition prod_twosided_disp_cat_id_mor
    : twosided_disp_cat_id_comp prod_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, tt).
  Defined.

  Definition prod_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_twosided_disp_cat_ob_mor.
    - exact prod_twosided_disp_cat_id_mor.
  Defined.

  Definition prod_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms prod_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply isapropunit.
    - apply isapropunit.
    - apply isapropunit.
    - apply isasetunit.
  Qed.

  Definition prod_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_twosided_disp_cat_data.
    - exact prod_twosided_disp_cat_axioms.
  Defined.
End ProductTwoSidedDispCat.
