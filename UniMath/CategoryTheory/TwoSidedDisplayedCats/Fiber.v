Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section FiberSet.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂)
          (HD : discrete_twosided_disp_cat D)
          (x : C₁)
          (y : C₂).

  Definition fiber_hset_twosided_disp_cat
    : hSet.
  Proof.
    use make_hSet.
    - exact (D x y).
    -
  Admitted.
End FiberSet.

Section FiberCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂)
          (x : C₁)
          (y : C₂).

  Definition fiber_twosided_disp_precat_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (D x y).
    - exact (λ xy₁ xy₂, xy₁ -->[ identity x ][ identity y ] xy₂).
  Defined.

  Definition fiber_twosided_disp_precat_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact fiber_twosided_disp_precat_ob_mor.
    - exact (λ xy, id_two_disp xy).
    - exact (λ _ _ _ f g,
             transportf
               (λ z, _ -->[ z ][ _ ] _)
               (id_left _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (id_left _)
                  (f ;;2 g))).
  Defined.

  Definition fiber_twosided_disp_is_precategory
    : is_precategory fiber_twosided_disp_precat_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split.
    - intros xy₁ xy₂ f ; cbn.
      admit.
    - intros xy₁ xy₂ f ; cbn.
      admit.
    - intros xy₁ xy₂ xy₃ xy₄ f g h ; cbn.
      admit.
  Admitted.

  Definition fiber_twosided_disp_precat
    : precategory.
  Proof.
    use make_precategory.
    - exact fiber_twosided_disp_precat_data.
    - exact fiber_twosided_disp_is_precategory.
  Defined.

  Definition fiber_twosided_disp_cat
    : category.
  Proof.
    use make_category.
    - exact fiber_twosided_disp_precat.
    - intros xy₁ xy₂ ; cbn.
      apply isaset_disp_mor.
  Defined.
End FiberCat.
