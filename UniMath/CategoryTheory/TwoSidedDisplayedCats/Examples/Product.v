(**********************************************************************************

 The product via two-sided displayed categories

 By taking the displayed objects and displayed morphisms to be inhabitants of the
 unit type, we obtain the product of two categories.

 Contents
 1. Definition via two-sided displayed categories
 2. Discreteness and univalence

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section ProductTwoSidedDispCat.
  Context (C₁ C₂ : category).

  (**
   1. Definition via two-sided displayed categories
   *)
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

  (**
   2. Discreteness and univalence
   *)
  Definition constant_twosided_disp_cat_is_iso
    : all_disp_mor_iso prod_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g Hf Hg fg.
    simple refine (_ ,, _ ,, _).
    - exact tt.
    - apply isapropunit.
    - apply isapropunit.
  Defined.

  Definition is_univalent_prod_twosided_disp_cat
    : is_univalent_twosided_disp_cat prod_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      apply isapropunit.
    - apply isasetunit.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply isapropunit.
  Qed.

  Definition discrete_prod_twosided_disp_cat
    : discrete_twosided_disp_cat prod_twosided_disp_cat.
  Proof.
    repeat split.
    - intro ; intros.
      apply isapropunit.
    - exact constant_twosided_disp_cat_is_iso.
    - exact is_univalent_prod_twosided_disp_cat.
  Qed.
End ProductTwoSidedDispCat.
