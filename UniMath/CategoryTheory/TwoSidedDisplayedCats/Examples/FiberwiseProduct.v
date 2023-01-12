Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section FiberwiseProduct.
  Context {C₁ C₂ : category}
          (D₁ D₂ : twosided_disp_cat C₁ C₂).

  Definition prod_of_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D₁ x y × D₂ x y).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g,
             pr1 xy₁ -->[ f ][ g ] pr1 xy₂
             ×
             pr2 xy₁ -->[ f ][ g ] pr2 xy₂).
  Defined.

  Definition prod_of_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp prod_of_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, id_two_disp (pr1 xy) ,, id_two_disp (pr2 xy)).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
             (pr1 fg₁ ;;2 pr1 fg₂) ,, (pr2 fg₁ ;;2 pr2 fg₂)).
  Defined.

  Definition prod_of_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_of_twosided_disp_cat_ob_mor.
    - exact prod_of_twosided_disp_cat_id_comp.
  Defined.

  Definition prod_of_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms prod_of_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      admit.
    - intro ; intros ; cbn.
      admit.
    - intro ; intros ; cbn.
      admit.
    - intro ; intros.
      apply isasetdirprod ; apply isaset_disp_mor.
  Admitted.

  Definition prod_of_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_of_twosided_disp_cat_data.
    - exact prod_of_twosided_disp_cat_axioms.
  Defined.
End FiberwiseProduct.
