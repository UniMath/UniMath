Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section ConstantTwoSidedDispCat.
  Context (C₁ C₂ D : category).

  Definition constant_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, D).
    - exact (λ _ _ _ _ z₁ z₂ _ _, z₁ --> z₂).
  Defined.

  Definition constant_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp constant_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ _, identity _).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂, h₁ · h₂).
  Defined.

  Definition constant_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact constant_twosided_disp_cat_ob_mor.
    - exact constant_twosided_disp_cat_id_comp.
  Defined.

  Definition constant_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms constant_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; unfold transportb ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply id_left.
    - intro ; intros ; unfold transportb ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply id_right.
    - intro ; intros ; unfold transportb ; cbn in *.
      rewrite !transportf_const ; cbn.
      apply assoc.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition constant_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact constant_twosided_disp_cat_data.
    - exact constant_twosided_disp_cat_axioms.
  Defined.
End ConstantTwoSidedDispCat.
