Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Definition rel_disp_cat_ob_mor
  : twosided_disp_cat_ob_mor SET SET.
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet) (Y : hSet), X → Y → hProp).
  - exact (λ (X₁ : hSet) X₂ (Y₁ : hSet) Y₂ R₁ R₂ f g,
           ∏ (x : X₁) (y : Y₁),
           R₁ x y → R₂ (f x) (g y)).
Defined.

Definition rel_disp_cat_id_comp
  : twosided_disp_cat_id_comp rel_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y R x y r, r).
  - exact (λ X₁ X₂ X₃ Y₁ Y₂ Y₃ R₁ R₂ R₃ f₁ f₂ g₁ g₂ α β x y r, β _ _ (α _ _ r)).
Defined.

Definition rel_disp_cat_data
  : twosided_disp_cat_data SET SET.
Proof.
  simple refine (_ ,, _).
  - exact rel_disp_cat_ob_mor.
  - exact rel_disp_cat_id_comp.
Defined.

Definition rel_disp_cat_axioms
  : twosided_disp_cat_axioms rel_disp_cat_data.
Proof.
  repeat split.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₂.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₂.
  - intros X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ R₁ R₂ R₃ R₄ f₁ f₂ f₃ g₁ g₂ g α β γ.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₄.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g ; cbn.
    use impred_isaset ; intro x.
    use impred_isaset ; intro y.
    use impred_isaset ; intro r.
    apply isasetaprop.
    apply R₂.
Qed.

Definition rel_disp_cat
  : twosided_disp_cat SET SET.
Proof.
  simple refine (_ ,, _).
  - exact rel_disp_cat_data.
  - exact rel_disp_cat_axioms.
Defined.
