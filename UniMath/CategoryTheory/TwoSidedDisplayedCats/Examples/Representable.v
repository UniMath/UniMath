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

Section LeftRepresentable.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition left_repr_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, F x --> y).
    - exact (λ x₁ x₂ y₁ y₂ f₁ f₂ g₁ g₂, f₁ · g₂ = #F g₁ · f₂).
  Defined.

  Definition left_repr_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp left_repr_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - intro ; intros ; cbn.
      rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ f₁ f₂ f₃ g₁ g₂ h₁ h₂ p q ; cbn in *.
      rewrite functor_comp.
      rewrite !assoc.
      rewrite p.
      rewrite !assoc'.
      rewrite q.
      apply idpath.
  Qed.

  Definition left_repr_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact left_repr_twosided_disp_cat_ob_mor.
    - exact left_repr_twosided_disp_cat_id_comp.
  Defined.

  Definition left_repr_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms left_repr_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; apply homset_property.
    - intro ; intros ; apply homset_property.
    - intro ; intros ; apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition left_repr_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact left_repr_twosided_disp_cat_data.
    - exact left_repr_twosided_disp_cat_axioms.
  Defined.
End LeftRepresentable.

Section RightRepresentable.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition right_repr_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, x --> F y).
    - exact (λ x₁ x₂ y₁ y₂ f₁ f₂ g₁ g₂, f₁ · #F g₂ = g₁ · f₂).
  Defined.

  Definition right_repr_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp right_repr_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - intro ; intros ; cbn.
      rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ f₁ f₂ f₃ g₁ g₂ h₁ h₂ p q ; cbn in *.
      rewrite functor_comp.
      rewrite !assoc.
      rewrite p.
      rewrite !assoc'.
      rewrite q.
      apply idpath.
  Qed.

  Definition right_repr_twosided_disp_cat_data
    : twosided_disp_cat_data C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact right_repr_twosided_disp_cat_ob_mor.
    - exact right_repr_twosided_disp_cat_id_comp.
  Defined.

  Definition right_repr_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms right_repr_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; apply homset_property.
    - intro ; intros ; apply homset_property.
    - intro ; intros ; apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition right_repr_twosided_disp_cat
    : twosided_disp_cat C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact right_repr_twosided_disp_cat_data.
    - exact right_repr_twosided_disp_cat_axioms.
  Defined.
End RightRepresentable.
