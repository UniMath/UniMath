(*********************************************************************************

 The underlying vertical 2-category of a strict double category

 Every strict double category `C` has an underlying vertical 2-category:
 - Objects: objects in `C`
 - 1-cells: vertical morphisms in `C`
 - 2-cells: squares in `C` whose horizontal sides are the horizontal identity
 All operations are inherited from `C`.

 Note: since every strict double category has a dual, we can also directly define
 the underlying horizontal 2-category. We do so by taking the underlying vertical
 2-category of the dual.

 Contents
 1. The underlying category
 2. The data of the 2-category
 3. The laws of the 2-category
 4. The underlying vertical 2-category

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.StrictDoubleCats.

Local Open Scope cat.
Local Open Scope strict_double_cat.

Section UnderlyingVerticalCategory.
  Context (C : strict_double_cat).

  (** * 1. The underlying category *)
  Definition strict_underlying_vertical_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, x -->v y).
  Defined.

  Definition strict_underlying_vertical_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact strict_underlying_vertical_precategory_ob_mor.
    - exact (λ x, s_identity_v x).
    - exact (λ _ _ _ v₁ v₂, v₁ ·v v₂).
  Defined.

  Proposition is_precategory_strict_underlying_vertical_two_cat_data
    : is_precategory strict_underlying_vertical_precategory_data.
  Proof.
    repeat split.
    - cbn ; intros x y f.
      apply s_id_v_left.
    - cbn ; intros x y f.
      apply s_id_v_right.
    - cbn ; intros w x y z f g h.
      apply s_assocl_v.
    - cbn ; intros w x y z f g h.
      apply s_assocr_v.
  Defined.

  (** * 2. The data of the 2-category *)
  Definition strict_underlying_vertical_two_cat_data
    : two_cat_data.
  Proof.
    use make_two_cat_data.
    - exact strict_underlying_vertical_precategory_data.
    - exact (λ x y v₁ v₂, s_square v₁ v₂ (s_identity_h x) (s_identity_h y)).
    - exact (λ x y v, s_id_h_square v).
    - exact (λ x y v₁ v₂ v₃ s₁ s₂,
             transportf_s_square
               (idpath _)
               (idpath _)
               (s_id_h_left _)
               (s_id_h_left _)
               (s₁ ⋆h s₂)).
    - exact (λ x y z v w₁ w₂ s, s_id_h_square v ⋆v s).
    - exact (λ x y z v₁ v₂ w s, s ⋆v s_id_h_square w).
  Defined.

  Definition strict_underlying_vertical_two_cat_category
    : two_cat_category.
  Proof.
    use make_two_cat_category.
    - exact strict_underlying_vertical_two_cat_data.
    - exact is_precategory_strict_underlying_vertical_two_cat_data.
    - abstract
        (intros x y ;
         apply homset_property).
  Defined.

  (** * 3. The laws of the 2-category *)
  Proposition vertical_two_cat_category_idto2mor
              {x y : C}
              {f g : x -->v y}
              (p : f = g)
    : idto2mor (C := strict_underlying_vertical_two_cat_data) p
      =
      transportf_s_square
        (idpath _)
        p
        (idpath _)
        (idpath _)
        (s_id_h_square f).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition two_cat_laws_strict_underlying_vertical_two_cat_category
    : two_cat_laws strict_underlying_vertical_two_cat_category.
  Proof.
    repeat split ; cbn -[transportf_s_square].
    - intros x y v₁ v₂ s.
      rewrite strict_square_id_left.
      rewrite transportfb_s_square.
      apply idpath.
    - intros x y v₁ v₂ s.
      rewrite strict_square_id_right.
      rewrite transportfb_s_square.
      apply idpath.
    - intros x y v₁ v₂ v₃ v₄ s₁ s₂ s₃.
      rewrite transportf_s_square_post_whisker_h.
      rewrite transportf_s_square_pre_whisker_h.
      rewrite !transportf_f_s_square.
      rewrite strict_square_assoc.
      unfold transportb_s_square.
      rewrite transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
    - intros x y z v₁ v₂.
      rewrite s_id_h_square_comp.
      apply idpath.
    - intros x y z v₁ v₂.
      rewrite s_id_h_square_comp.
      apply idpath.
    - intros x y z v w₁ w₂ w₄ s₁ s₂.
      rewrite comp_h_square_comp.
      rewrite strict_square_id_left.
      unfold transportb_s_square.
      refine (!_).
      exact (transportf_s_square_post_whisker_v'
                 _ _ _ _ _ _ _).
    - intros x y z v₁ v₂ v₃ w s₁ s₂.
      rewrite comp_h_square_comp.
      rewrite strict_square_id_left.
      unfold transportb_s_square.
      rewrite (transportf_s_square_pre_whisker_v' _ _ _ _ (s_id_h_left (s_identity_h z))).
      apply idpath.
    - intros x y z v₁ v₂ w₁ w₂ s₁ s₂.
      rewrite !comp_h_square_comp.
      rewrite !strict_square_id_left.
      rewrite !strict_square_id_right.
      use transportf_s_square_eq.
      assert (s_id_h_left (s_identity_h x) = s_id_h_right (s_identity_h x)) as r.
      {
        apply isaset_hor_mor_strict_double_cat.
      }
      rewrite r ; clear r.
      assert (s_id_h_left (s_identity_h y) = s_id_h_right (s_identity_h y)) as r.
      {
        apply isaset_hor_mor_strict_double_cat.
      }
      rewrite r ; clear r.
      apply maponpaths.
      use transportf_s_square_eq.
      apply idpath.
    - intros x y v₁ v₂ s.
      rewrite !vertical_two_cat_category_idto2mor.
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_post_whisker_h' _ _ _ _ _ _ (s_id_v_left _) _ _).
      }
      rewrite strict_square_id_right.
      rewrite s_id_h_square_id.
      rewrite s_square_id_left_v.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_pre_whisker_h' _ _ _ _ (idpath _) _ _ _ _).
      }
      rewrite strict_square_id_left.
      unfold transportb_s_square.
      rewrite !transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
    - intros x y v₁ v₂ s.
      rewrite !vertical_two_cat_category_idto2mor.
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_post_whisker_h' _ _ _ _ _ _ (s_id_v_right _) _ _).
      }
      rewrite strict_square_id_right.
      rewrite s_id_h_square_id.
      rewrite s_square_id_right_v.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_pre_whisker_h' _ _ _ _ (idpath _) _ _ _ _).
      }
      rewrite strict_square_id_left.
      unfold transportb_s_square.
      rewrite !transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u v w₁ w₂ s.
      rewrite !vertical_two_cat_category_idto2mor.
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_post_whisker_h' _ _ _ _ _ _ (s_assocl_v _ _ _) _ _).
      }
      rewrite strict_square_id_right.
      rewrite s_square_assoc_v.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_pre_whisker_h' _ _ _ _ (idpath _) _ _ _ _).
      }
      rewrite strict_square_id_left.
      rewrite s_id_h_square_comp.
      unfold transportb_s_square.
      rewrite !transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u v₁ v₂ w s.
      rewrite !vertical_two_cat_category_idto2mor.
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_post_whisker_h' _ _ _ _ _ _ (s_assocl_v _ _ _) _ _).
      }
      rewrite strict_square_id_right.
      rewrite s_square_assoc_v.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_pre_whisker_h' _ _ _ _ (idpath _) _ _ _ _).
      }
      rewrite strict_square_id_left.
      unfold transportb_s_square.
      rewrite !transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u₁ u₂ v w s.
      rewrite !vertical_two_cat_category_idto2mor.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_post_whisker_h' _ _ _ _ _ _ (s_assocl_v _ _ _) _ _).
      }
      rewrite strict_square_id_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (transportf_s_square_pre_whisker_h' _ _ _ _ (idpath _) _ _ _ _).
      }
      rewrite strict_square_id_left.
      rewrite s_id_h_square_comp.
      rewrite s_square_assoc_v.
      unfold transportb_s_square.
      rewrite !transportf_f_s_square.
      use transportf_s_square_eq.
      apply idpath.
  Qed.

  (** * 4. The underlying vertical 2-category *)
  Definition strict_underlying_vertical_two_precat
    : two_precat.
  Proof.
    use make_two_precat.
    - exact strict_underlying_vertical_two_cat_category.
    - exact two_cat_laws_strict_underlying_vertical_two_cat_category.
  Defined.

  Definition strict_underlying_vertical_two_cat
    : two_cat.
  Proof.
    use make_two_cat.
    - exact strict_underlying_vertical_two_precat.
    - intros x y f g.
      apply isaset_disp_mor.
  Defined.

  Proposition is_strict_strict_underlying_vertical_two_cat
    : is_two_setcat strict_underlying_vertical_two_cat.
  Proof.
    apply isaset_ob_strict_double_cat.
  Qed.

  Definition strict_underlying_vertical_two_setcat
    : two_setcat
    := make_two_setcat
         strict_underlying_vertical_two_cat
         is_strict_strict_underlying_vertical_two_cat.
End UnderlyingVerticalCategory.
