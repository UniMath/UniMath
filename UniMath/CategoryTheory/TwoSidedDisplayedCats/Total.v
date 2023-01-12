Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section TotalOfTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition total_twosided_disp_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (∑ (x : C₁) (y : C₂), D x y).
    - exact (λ xy₁ xy₂,
             ∑ (f : pr1 xy₁ --> pr1 xy₂)
               (g : pr12 xy₁ --> pr12 xy₂),
             pr22 xy₁ -->[ f ][ g ] pr22 xy₂).
  Defined.

  Definition total_twosided_disp_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact total_twosided_disp_precategory_ob_mor.
    - exact (λ xy,
             identity (pr1 xy)
             ,,
             identity (pr12 xy)
             ,,
             id_two_disp (pr22 xy)).
    - exact (λ xy₁ xy₂ xy₃ fg₁ fg₂,
             pr1 fg₁ · pr1 fg₂
             ,,
             pr12 fg₁ · pr12 fg₂
             ,,
             pr22 fg₁ ;;2 pr22 fg₂).
  Defined.

  Definition total_twosided_disp_is_precategory
    : is_precategory total_twosided_disp_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_left.
      + apply id_left.
      + apply id_two_disp_left.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_right.
      + apply id_right.
      + apply id_two_disp_right.
    - intros xy₁ xy₂ xy₃ xy₄ fg₁ fg₂ fg₃.
      use total2_paths_2_b.
      + apply assoc.
      + apply assoc.
      + apply assoc_two_disp.
  Qed.

  Definition total_twosided_disp_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact total_twosided_disp_precategory_data.
    - exact total_twosided_disp_is_precategory.
  Defined.

  Definition has_homsets_total_twosided_disp_category
    : has_homsets total_twosided_disp_precategory_ob_mor.
  Proof.
    intros xy₁ xy₂.
    apply isaset_total2.
    - apply homset_property.
    - intro.
      apply isaset_total2.
      + apply homset_property.
      + intro.
        apply isaset_disp_mor.
  Defined.

  Definition total_twosided_disp_category
    : category.
  Proof.
    use make_category.
    - exact total_twosided_disp_precategory.
    - exact has_homsets_total_twosided_disp_category.
  Defined.

  Definition twosided_disp_category_pr1_data
    : functor_data total_twosided_disp_category C₁.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr1 xy).
    - exact (λ xy₁ xy₂ fg, pr1 fg).
  Defined.

  Definition twosided_disp_category_pr1_is_functor
    : is_functor twosided_disp_category_pr1_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr1
    : total_twosided_disp_category ⟶ C₁.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr1_data.
    - exact twosided_disp_category_pr1_is_functor.
  Defined.

  Definition twosided_disp_category_pr2_data
    : functor_data total_twosided_disp_category C₂.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr12 xy).
    - exact (λ xy₁ xy₂ fg, pr12 fg).
  Defined.

  Definition twosided_disp_category_pr2_is_functor
    : is_functor twosided_disp_category_pr2_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr2
    : total_twosided_disp_category ⟶ C₂.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr2_data.
    - exact twosided_disp_category_pr2_is_functor.
  Defined.

  Section IsoTotal.
    Context {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            {xy₁ : D x₁ y₁}
            {xy₂ : D x₂ y₂}
            {f : x₁ --> x₂}
            {Hf : is_z_isomorphism f}
            {g : y₁ --> y₂}
            {Hg : is_z_isomorphism g}
            (fg : xy₁ -->[ f ][ g ] xy₂)
            (Hfg : is_iso_twosided_disp Hf Hg fg).

    Let total_fg : total_twosided_disp_category ⟦ (x₁ ,, y₁ ,, xy₁) , (x₂ ,, y₂ ,, xy₂) ⟧
        := f ,, g ,, fg.
    Let f_z_iso : z_iso x₁ x₂ := f ,, Hf.
    Let g_z_iso : z_iso y₁ y₂ := g ,, Hg.

    Definition is_z_iso_total_twosided_disp_cat_inv
      : total_twosided_disp_category ⟦ (x₂ ,, y₂ ,, xy₂) , (x₁ ,, y₁ ,, xy₁) ⟧
      := inv_from_z_iso f_z_iso
         ,,
         inv_from_z_iso g_z_iso
         ,,
         iso_inv_twosided_disp Hfg.

    Definition is_z_iso_total_twosided_disp_cat_inv_right
      : total_fg · is_z_iso_total_twosided_disp_cat_inv = identity _.
    Proof.
      use total2_paths_2_b ; cbn.
      - apply (z_iso_inv_after_z_iso f_z_iso).
      - apply (z_iso_inv_after_z_iso g_z_iso).
      - apply inv_after_iso_twosided_disp.
    Qed.

    Definition is_z_iso_total_twosided_disp_cat_inv_left
      : is_z_iso_total_twosided_disp_cat_inv · total_fg = identity _.
    Proof.
      use total2_paths_2_b ; cbn.
      - apply (z_iso_after_z_iso_inv f_z_iso).
      - apply (z_iso_after_z_iso_inv g_z_iso).
      - apply iso_after_inv_twosided_disp.
    Qed.

    Definition is_z_iso_total_twosided_disp_cat
      : is_z_isomorphism total_fg.
    Proof.
      simple refine (is_z_iso_total_twosided_disp_cat_inv ,, _ ,, _).
      - apply is_z_iso_total_twosided_disp_cat_inv_right.
      - apply is_z_iso_total_twosided_disp_cat_inv_left.
    Defined.
  End IsoTotal.
End TotalOfTwoSidedDispCat.
