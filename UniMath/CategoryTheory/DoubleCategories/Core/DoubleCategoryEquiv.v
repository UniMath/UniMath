(********************************************************************************

 Equivalence of different notions of double categories

 There are multiple ways to phrase the definition of a double category. One of
 them, given in `DoubleCategories.Core.DoubleCategories`, is a direct definition
 which follows the style of how categories are defied in UniMath. The other,
 which is in `TwoSidedDisplayedCats.DoubleCategory`, makes use 2-sided displayed
 categories. In this file, we prove an equivalence of these notions.

 Note:
 - `double_cat`: defined via 2-sided displayed categories
 - `doublecategory`: directed definition

 Contents
 1. From `double_cat` to `doublecategory`

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DoubleCategory.
Require Import UniMath.CategoryTheory.DoubleCategories.Core.DoubleCategories.

Local Open Scope cat.

(**
 1. From `double_cat` to `doublecategory`
 *)
Section FromDoubleCategoryViaTwoSided.
  Context (C : double_cat).

  Definition double_cat_to_predoublecategory_ob_mor_hor
    : predoublecategory_ob_mor_hor.
  Proof.
    simple refine (_ ,, _).
    - exact (ob C).
    - exact (λ x y, x --> y).
  Defined.

  Definition double_cat_to_predoublecategory_ob_mor_data
    : predoublecategory_ob_mor_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_hor.
    - exact (λ x y, x -->v y).
  Defined.

  Definition double_cat_to_predoublecategory_hor_id_comp
    : predoublecategory_hor_id_comp
        double_cat_to_predoublecategory_ob_mor_data.
  Proof.
    split.
    - exact (λ x, identity x).
    - exact (λ x y z f g, f · g).
  Defined.

  Definition double_cat_to_predoublecategory_hor_precat_data
    : predoublecategory_hor_precat_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_data.
    - exact double_cat_to_predoublecategory_hor_id_comp.
  Defined.

  Proposition is_predoublecategory_hor_double_cat
    : is_predoublecategory_hor
        double_cat_to_predoublecategory_hor_precat_data.
  Proof.
    repeat split.
    - intros x y f ; cbn.
      apply id_left.
    - intros x y f ; cbn.
      apply id_right.
    - intros w x y z f g h ; cbn.
      apply assoc.
    - intros w x y z f g h ; cbn.
      apply assoc'.
  Qed.

  Definition double_cat_to_predoublecategory_hor
    : predoublecategory_hor.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_precat_data.
    - exact is_predoublecategory_hor_double_cat.
  Defined.

  Definition double_cat_to_predoublecategory_ver_id_comp
    : predoublecategory_ver_id_comp double_cat_to_predoublecategory_hor.
  Proof.
    split.
    - exact (λ x, double_id x).
    - exact (λ x y z f g, f ·v g).
  Defined.

  Definition double_cat_to_predoublecategory_hor_cat_ver_precat_data
    : predoublecategory_hor_cat_ver_precat_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor.
    - exact double_cat_to_predoublecategory_ver_id_comp.
  Defined.

  Definition double_cat_to_predoublecategory_ob_mor_sq_data
    : predoublecategory_ob_mor_sq_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_cat_ver_precat_data.
    - exact (λ w x y z f₁ g₁ g₂ f₂, g₁ -->[ f₁ ][ f₂ ] g₂).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_id_comp
    : predoublecategory_sq_hor_id_comp
        double_cat_to_predoublecategory_ob_mor_sq_data.
  Proof.
    split.
    - exact (λ x y f, id_two_disp _).
    - exact (λ x₁ x₂ y₁ y₂ z₁ z₂ f₁ f₂ f₃ g₁ h₁ g₂ h₂ α β, α ;;2 β).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_data
    : predoublecategory_sq_hor_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_ob_mor_sq_data.
    - exact double_cat_to_predoublecategory_sq_hor_id_comp.
  Defined.

  Proposition is_predoublecategory_hor_sq_double_cat
    : is_predoublecategory_hor_sq
        double_cat_to_predoublecategory_sq_hor_data.
  Proof.
    repeat split.
    - intros w x y z f g h k α.
      refine (_ @ !(id_two_disp_left_alt _)).
      cbn.
      unfold hor_trans_id_left_sq, boundary_sq_transport ; cbn.
      rewrite twosided_swap_transport.
      rewrite !twosided_prod_transport.
      apply maponpaths_2.
      apply isasetdirprod ; apply Categories.homset_property.
    - intros w x y z f g h k α.
      refine (_ @ !(id_two_disp_right_alt _)).
      cbn.
      unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn.
      rewrite twosided_swap_transport.
      rewrite !twosided_prod_transport.
      apply maponpaths_2.
      apply isasetdirprod ; apply Categories.homset_property.
    - intros w₁ x₁ y₁ z₁ w₂ x₂ y₂ z₂ f₁ g₁ h₁ f₂ g₂ h₂ k₁ k₂ k₃ k₄ α β χ.
      refine (_ @ !(assoc_two_disp_alt _ _ _)).
      unfold hor_trans_assoc_sq, boundary_sq_transport ; cbn.
      rewrite twosided_swap_transport.
      rewrite !twosided_prod_transport.
      apply maponpaths_2.
      apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Definition double_cat_to_predoublecategory_hor_sq
    : predoublecategory_hor_sq.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_data.
    - exact is_predoublecategory_hor_sq_double_cat.
  Defined.

  Definition double_cat_predoublecategory_sq_ver_id_comp
    : predoublecategory_sq_ver_id_comp
        double_cat_to_predoublecategory_hor_sq.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, double_cat_id_mor f).
    - exact (λ x₁ x₂ y₁ y₂ z₁ z₂ f₁ f₂ f₃ g₁ h₁ g₂ h₂ α β, double_cat_square_comp α β).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_ver_data
    : predoublecategory_sq_hor_ver_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_hor_sq.
    - exact double_cat_predoublecategory_sq_ver_id_comp.
  Defined.

  Proposition has_predoublecategory_sq_hor_ver_unit_assoc_double_cat
    : has_predoublecategory_sq_hor_ver_unit_assoc
        double_cat_to_predoublecategory_sq_hor_ver_data.
  Proof.
    repeat split.
    - intros x y f.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + apply double_lunitor.
      + apply double_linvunitor.
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_lunitor_linvunitor _) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_linvunitor_lunitor _) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
    - intros x y f.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + apply double_runitor.
      + apply double_rinvunitor.
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_runitor_rinvunitor _) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_rinvunitor_runitor _) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
    - intros w x y z f g h.
      simple refine (_ ,, _ ,, _ ,, _) ; cbn.
      + apply double_rassociator.
      + apply double_lassociator.
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_rassociator_lassociator f g h) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
      + abstract
          (unfold hor_trans_id_right_sq, boundary_sq_transport ; cbn ;
           refine (_ @ double_lassociator_rassociator f g h) ;
           rewrite twosided_swap_transport ;
           rewrite !twosided_prod_transport ;
           apply maponpaths_2 ;
           apply isasetdirprod ; apply Categories.homset_property).
  Defined.

  Definition double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data
    : predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    simple refine (_ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_ver_data.
    - exact has_predoublecategory_sq_hor_ver_unit_assoc_double_cat.
  Defined.

  Proposition predoublecategory_ver_left_unitor_naturality_double_cat
    : predoublecategory_ver_left_unitor_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros w x y z f g h k α.
    unfold hor_trans_id_right_sq, hor_trans_id_left_sq, boundary_sq_transport ; cbn.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(double_cat_lunitor_nat α)).
    }
    rewrite !twosided_swap_transport.
    unfold transportb.
    rewrite !twosided_prod_transport.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Proposition predoublecategory_ver_right_unitor_naturality_double_cat
    : predoublecategory_ver_right_unitor_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros w x y z f g h k α.
    unfold hor_trans_id_right_sq, hor_trans_id_left_sq, boundary_sq_transport ; cbn.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(double_cat_runitor_nat α)).
    }
    rewrite !twosided_swap_transport.
    unfold transportb.
    rewrite !twosided_prod_transport.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Proposition predoublecategory_ver_assoc_naturality_double_cat
    : predoublecategory_ver_assoc_naturality
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ f₁ f₂ h₁ h₂ k₁ k₂ g₁ g₂ g₃ g₄ α β γ.
    unfold hor_trans_id_right_sq, hor_trans_id_left_sq, boundary_sq_transport ; cbn.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(double_cat_rassociator_nat α β γ)).
    }
    rewrite !twosided_swap_transport.
    unfold transportb.
    rewrite !twosided_prod_transport.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Proposition predoublecategory_ver_unitor_coherence_double_cat
    : predoublecategory_ver_unitor_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros x y z f g.
    unfold hor_trans_id_right_sq, hor_trans_id_left_sq, boundary_sq_transport ; cbn.
    refine (_ @ double_cat_triangle f g).
    rewrite !twosided_swap_transport.
    unfold transportb.
    rewrite !twosided_prod_transport.
    apply maponpaths_2.
    apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Proposition predoublecategory_ver_assoc_coherence_double_cat
    : predoublecategory_ver_assoc_coherence
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros v w x y z f g h k.
    unfold hor_trans_id_right_sq, hor_trans_id_left_sq, boundary_sq_transport ; cbn.
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths.
      exact (!(double_cat_pentagon f g h k)).
    }
    unfold transportb.
    refine (!_).
    etrans.
    {
      rewrite twosided_swap_transport.
      rewrite twosided_prod_transport.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths.
      rewrite twosided_prod_transport.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite twosided_swap_transport.
      rewrite twosided_prod_transport.
      rewrite transport_f_f.
      apply idpath.
    }
    rewrite twosided_swap_transport.
    rewrite twosided_prod_transport.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply Categories.homset_property.
  Qed.

  Proposition predoublecategory_interchange_double_cat
    : predoublecategory_interchange
        double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
  Proof.
    intros x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ fx gx fy gy fz gz h₁ k₁ h₂ k₂ h₃ k₃ α β γ δ ; cbn in *.
    exact (double_cat_interchange α β γ δ).
  Qed.

  Definition double_cat_to_predoublecategory
    : predoublecategory.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact double_cat_to_predoublecategory_sq_hor_ver_unit_assoc_data.
    - exact predoublecategory_ver_left_unitor_naturality_double_cat.
    - exact predoublecategory_ver_right_unitor_naturality_double_cat.
    - exact predoublecategory_ver_assoc_naturality_double_cat.
    - exact predoublecategory_ver_unitor_coherence_double_cat.
    - exact predoublecategory_ver_assoc_coherence_double_cat.
    - exact predoublecategory_interchange_double_cat.
  Defined.

  Definition double_cat_to_doublecategory
    : doublecategory.
  Proof.
    use make_doublecategory.
    - exact double_cat_to_predoublecategory.
    - intros x y.
      apply Categories.homset_property.
    - intros x y.
      use isaset_total2 ; [ | intro f ; use isaset_total2 ].
      + apply Categories.homset_property.
      + apply Categories.homset_property.
      + intro g ; cbn.
        apply isaset_disp_mor.
  Defined.
End FromDoubleCategoryViaTwoSided.
