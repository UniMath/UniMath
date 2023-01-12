Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

Section DispCatOnTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D₁ : twosided_disp_cat C₁ C₂)
          (D₂ : disp_cat (total_twosided_disp_category D₁)).

  Definition sigma_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, ∑ (xy : D₁ x y), D₂ (x ,, y ,, xy)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g,
             ∑ (fg : pr1 xy₁ -->[ f ][ g ] pr1 xy₂),
             pr2 xy₁ -->[ f ,, g ,, fg ] pr2 xy₂).
  Defined.

  Definition sigma_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp sigma_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - simple refine (λ x y xy, id_two_disp (pr1 xy) ,, _).
      apply (@id_disp (total_twosided_disp_category D₁) D₂).
    -
  Admitted.

  Definition sigma_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact sigma_twosided_disp_cat_ob_mor.
    - exact sigma_twosided_disp_cat_id_comp.
  Defined.

  Definition sigma_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact sigma_twosided_disp_cat_data.
    -
  Admitted.
End DispCatOnTwoSidedDispCat.
