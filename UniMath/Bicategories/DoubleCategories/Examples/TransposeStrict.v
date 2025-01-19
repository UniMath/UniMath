(*********************************************************************************

 The transpose of a strict double category

 If we have a strict double category `C`, then we can define its tranpose as follows:
 - Objects: objects in `C`
 - Vertical morphisms: horizontal morphisms in `C`
 - Horizontal morphisms: vertical morphisms in `C`
 - Squares: squares in `C`
 Concretely, we switch the roles of the horizontal and the vertical morphisms.
 In this file, we construct this strict double category.

 Contents
 1. The precategory
 2. The 2-sided displayed category
 3. The horizontal identity
 4. Horizontal composition
 5. Double category laws
 6. The transpose double category

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.StrictDoubleCats.

Local Open Scope cat.
Local Open Scope strict_double_cat.

Section Transpose.
  Context (C : strict_double_cat).

  (** * 1. The precategory *)
  Definition transpose_strict_double_cat_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, x -->h y).
  Defined.

  Definition transpose_strict_double_cat_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact transpose_strict_double_cat_precategory_ob_mor.
    - exact (λ x, s_identity_h x).
    - exact (λ x y z h k, h ·h k).
  Defined.

  Proposition is_precategory_transpose_strict_double_cat_precategory_data
    : is_precategory transpose_strict_double_cat_precategory_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split.
    - intros x y f ; cbn.
      apply s_id_h_left.
    - intros x y f ; cbn.
      apply s_id_h_right.
    - intros w x y z f g h ; cbn.
      apply s_assocl_h.
  Defined.

  Definition transpose_strict_double_cat_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact transpose_strict_double_cat_precategory_data.
    - exact is_precategory_transpose_strict_double_cat_precategory_data.
  Defined.

  Definition transpose_strict_double_cat_category
    : category.
  Proof.
    use make_category.
    - exact transpose_strict_double_cat_precategory.
    - intros x y.
      apply isaset_hor_mor_strict_double_cat.
  Defined.

  Definition transpose_strict_double_cat_setcategory
    : setcategory.
  Proof.
    use make_setcategory.
    - exact transpose_strict_double_cat_category.
    - apply isaset_ob_strict_double_cat.
  Defined.

  (** * 2. The 2-sided displayed category *)
  Definition transpose_strict_double_cat_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor
        transpose_strict_double_cat_setcategory
        transpose_strict_double_cat_setcategory.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ x y, x -->v y).
    - exact (λ x₁ x₂ y₁ y₂ v₁ v₂ h₁ h₂, s_square v₁ v₂ h₁ h₂).
  Defined.

  Definition transpose_strict_double_cat_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp transpose_strict_double_cat_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y v, s_id_h_square v).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ v₃ h₁ h₂ h₃ h₄ s₁ s₂, _) ; cbn in *.
      exact (s₁ ⋆h s₂).
  Defined.

  Definition transpose_strict_double_cat_twosided_disp_cat_data
    : twosided_disp_cat_data
        transpose_strict_double_cat_setcategory
        transpose_strict_double_cat_setcategory.
  Proof.
    simple refine (_ ,, _).
    - exact transpose_strict_double_cat_twosided_disp_cat_ob_mor.
    - exact transpose_strict_double_cat_twosided_disp_cat_id_comp.
  Defined.

  Proposition transpose_strict_double_cat_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms transpose_strict_double_cat_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ v₁ v₂ h k s ; cbn in *.
      rewrite strict_square_id_left.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ v₁ v₂ h k s ; cbn in *.
      rewrite strict_square_id_right.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ v₁ v₂ v₃ v₄ h₁ h₂ h₃ k₁ k₂ k₃ s₁ s₂ s₃ ; cbn in *.
      rewrite strict_square_assoc.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ v₁ v₂ h k ; cbn.
      apply isaset_s_square.
  Qed.

  Definition transpose_strict_double_cat_twosided_disp_cat
    : twosided_disp_cat
        transpose_strict_double_cat_setcategory
        transpose_strict_double_cat_setcategory.
  Proof.
    simple refine (_ ,, _).
    - exact transpose_strict_double_cat_twosided_disp_cat_data.
    - exact transpose_strict_double_cat_twosided_disp_cat_axioms.
  Defined.

  (** * 3. The horizontal identity *)
  Definition transpose_strict_double_cat_hor_id_data
    : hor_id_data transpose_strict_double_cat_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - exact (λ x, s_identity_v _).
    - exact (λ x y h, s_id_v_square h).
  Defined.

  Proposition transpose_strict_double_cat_hor_id_laws
    : hor_id_laws transpose_strict_double_cat_hor_id_data.
  Proof.
    split ; cbn.
    - intro x.
      rewrite s_id_h_square_id.
      apply idpath.
    - intros x y z h k.
      rewrite s_comp_h_square_id.
      apply idpath.
  Qed.

  Definition transpose_strict_double_cat_hor_id
    : hor_id transpose_strict_double_cat_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact transpose_strict_double_cat_hor_id_data.
    - exact transpose_strict_double_cat_hor_id_laws.
  Defined.

  (** * 4. Horizontal composition *)
  Definition transpose_strict_double_cat_hor_comp_data
    : hor_comp_data transpose_strict_double_cat_twosided_disp_cat.
  Proof.
    use make_hor_comp_data ; cbn.
    - exact (λ x y z v₁ v₂, v₁ ·v v₂).
    - exact (λ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ h₃ v₁ v₂ w₁ w₂ s₁ s₂, s₁ ⋆v s₂).
  Defined.

  Proposition transpose_strict_double_cat_hor_comp_laws
    : hor_comp_laws transpose_strict_double_cat_hor_comp_data.
  Proof.
    split ; cbn.
    - intros x y z v₁ v₂.
      rewrite s_id_h_square_comp.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ v₁ v₁' v₂ v₂' v₃ v₃' h₁ h₂ k₁ k₂ l₁ l₂ s₁ s₁' s₂ s₂'.
      rewrite comp_h_square_comp.
      apply idpath.
  Qed.

  Definition transpose_strict_double_cat_hor_comp
    : hor_comp transpose_strict_double_cat_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact transpose_strict_double_cat_hor_comp_data.
    - exact transpose_strict_double_cat_hor_comp_laws.
  Defined.

  (** * 5. Double category laws *)
  Proposition transpose_strict_double_cat_id_left
    : strict_double_cat_id_left
        transpose_strict_double_cat_hor_id
        transpose_strict_double_cat_hor_comp.
  Proof.
    intros x y v ; cbn in v ; cbn.
    apply s_id_v_left.
  Defined.

  Proposition transpose_strict_double_cat_id_right
    : strict_double_cat_id_right
        transpose_strict_double_cat_hor_id
        transpose_strict_double_cat_hor_comp.
  Proof.
    intros x y v ; cbn in v ; cbn.
    apply s_id_v_right.
  Defined.

  Proposition transpose_strict_double_cat_assoc
    : strict_double_cat_assoc transpose_strict_double_cat_hor_comp.
  Proof.
    intros w x y z v₁ v₂ v₃ ; cbn.
    apply s_assocl_v.
  Defined.

  Proposition transpose_strict_double_cat_id_left_square
    : strict_double_cat_id_left_square transpose_strict_double_cat_id_left.
  Proof.
    intros x₁ x₂ y₁ y₂ v₁ v₂ h k s ; cbn.
    apply s_square_id_left_v.
  Qed.

  Proposition transpose_strict_double_cat_id_right_square
    : strict_double_cat_id_right_square transpose_strict_double_cat_id_right.
  Proof.
    intros x₁ x₂ y₁ y₂ v₁ v₂ h k s ; cbn.
    apply s_square_id_right_v.
  Qed.

  Proposition transpose_strict_double_cat_assoc_square
    : strict_double_cat_assoc_square transpose_strict_double_cat_assoc.
  Proof.
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ vw vx vy vz h₁ h₂ h₃ k₁ k₂ k₃ s₁ s₂ s₃ ; cbn.
    apply s_square_assoc_v.
  Defined.

  (** * 6. The dual double category *)
  Definition transpose_strict_double_cat
    : strict_double_cat.
  Proof.
    use make_strict_double_cat.
    - exact transpose_strict_double_cat_setcategory.
    - exact transpose_strict_double_cat_twosided_disp_cat.
    - intros x y.
      apply isaset_ver_mor_strict_double_cat.
    - exact transpose_strict_double_cat_hor_id.
    - exact transpose_strict_double_cat_hor_comp.
    - exact transpose_strict_double_cat_id_left.
    - exact transpose_strict_double_cat_id_right.
    - exact transpose_strict_double_cat_assoc.
    - exact transpose_strict_double_cat_id_left_square.
    - exact transpose_strict_double_cat_id_right_square.
    - exact transpose_strict_double_cat_assoc_square.
  Defined.
End Transpose.
