(************************************************************************************

 The product of double categories

 In this file, we define the product of double categories. Given double categories
 `D₁` and `D₂`, the product of `D₁` and `D₂` is defined as follows:
 - Objects: pairs of objects in `D₁` and `D₂`
 - Vertical morphisms: pairs of vertical morphisms in `D₁` and `D₂`
 - Horizontal morphisms: pairs of horizontal morphisms in `D₁` and `D₂`
 - Squares: pairs of squares in `D₁` and `D₂`
 The operations are defined coordinate-wise.

 We also verify the universal property of products. More specifically, the product
 of double categories is the product in the bicategory of double categories.

 Contents
 1. Horizontal identity and composition
 2. Unitors and associator
 3. The triangle and pentagon
 4. The product of double categories
 5. Projections
 6. Pairing
 7. Pairing of double transformations
 8. Products of double categories

 ************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ProdOfTwosidedDispCat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.Basics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleTransformation.
Require Import UniMath.Bicategories.DoubleCategories.Core.BicatOfDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.InvertiblesAndEquivalences.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.Variations.

Local Open Scope cat.
Local Open Scope double_cat.

Section ProdOfDoubleCat.
  Context (D₁ D₂ : double_cat).

  (** * 1. Horizontal identity and composition *)
  Definition prod_double_cat_hor_id_data
    : hor_id_data (twosided_disp_cat_product (hor_mor D₁) (hor_mor D₂)).
  Proof.
    use make_hor_id_data.
    - exact (λ wx, identity_h (pr1 wx) ,, identity_h (pr2 wx)).
    - exact (λ wx yz fg, id_h_square (pr1 fg) ,, id_h_square (pr2 fg)).
  Defined.

  Proposition prod_double_cat_hor_id_laws
    : hor_id_laws prod_double_cat_hor_id_data.
  Proof.
    split.
    - intros x.
      use dirprodeq ; cbn.
      + apply id_h_square_id.
      + apply id_h_square_id.
    - intros x y z f g.
      use dirprodeq ; cbn.
      + apply id_h_square_comp.
      + apply id_h_square_comp.
  Qed.

  Definition prod_double_cat_hor_id
    : hor_id (twosided_disp_cat_product (hor_mor D₁) (hor_mor D₂)).
  Proof.
    use make_hor_id.
    - exact prod_double_cat_hor_id_data.
    - exact prod_double_cat_hor_id_laws.
  Defined.

  Definition prod_double_cat_hor_comp_data
    : hor_comp_data (twosided_disp_cat_product (hor_mor D₁) (hor_mor D₂)).
  Proof.
    use make_hor_comp_data.
    - exact (λ xy₁ xy₂ xy₃ fg hk, pr1 fg ·h pr1 hk ,, pr2 fg ·h pr2 hk).
    - exact (λ x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂,
             comp_h_square (pr1 s₁) (pr1 s₂)
             ,,
             comp_h_square (pr2 s₁) (pr2 s₂)).
  Defined.

  Proposition prod_double_cat_hor_comp_laws
    : hor_comp_laws prod_double_cat_hor_comp_data.
  Proof.
    split.
    - intros.
      use dirprodeq ; cbn.
      + apply comp_h_square_id.
      + apply comp_h_square_id.
    - intros.
      use dirprodeq ; cbn.
      + apply comp_h_square_comp.
      + apply comp_h_square_comp.
  Qed.

  Definition prod_double_cat_hor_comp
    : hor_comp (twosided_disp_cat_product (hor_mor D₁) (hor_mor D₂)).
  Proof.
    use make_hor_comp.
    - exact prod_double_cat_hor_comp_data.
    - exact prod_double_cat_hor_comp_laws.
  Defined.

  (** * 2. Unitors and associator *)
  Definition prod_double_cat_lunitor_data
    : double_lunitor_data prod_double_cat_hor_id prod_double_cat_hor_comp.
  Proof.
    simple refine (λ x y h, (lunitor_h (pr1 h) ,, lunitor_h (pr2 h)) ,, _).
    use is_isotwosided_disp_twosided_disp_cat_product.
    - refine (linvunitor_h (pr1 h) ,, _ ,, _).
      + apply lunitor_linvunitor_h.
      + apply linvunitor_lunitor_h.
    - refine (linvunitor_h (pr2 h) ,, _ ,, _).
      + apply lunitor_linvunitor_h.
      + apply linvunitor_lunitor_h.
  Defined.

  Proposition prod_double_cat_lunitor_laws
    : double_lunitor_laws prod_double_cat_lunitor_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_twosided_disp_cat_product.
    use dirprodeq ; cbn.
    - refine (_ @ !(lunitor_square _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
    - refine (_ @ !(lunitor_square _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  Definition prod_double_cat_lunitor
    : double_cat_lunitor prod_double_cat_hor_id prod_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact prod_double_cat_lunitor_data.
    - exact prod_double_cat_lunitor_laws.
  Defined.

  Definition prod_double_cat_runitor_data
    : double_runitor_data prod_double_cat_hor_id prod_double_cat_hor_comp.
  Proof.
    simple refine (λ x y h, (runitor_h (pr1 h) ,, runitor_h (pr2 h)) ,, _).
    use is_isotwosided_disp_twosided_disp_cat_product.
    - refine (rinvunitor_h (pr1 h) ,, _ ,, _).
      + apply runitor_rinvunitor_h.
      + apply rinvunitor_runitor_h.
    - refine (rinvunitor_h (pr2 h) ,, _ ,, _).
      + apply runitor_rinvunitor_h.
      + apply rinvunitor_runitor_h.
  Defined.

  Proposition prod_double_cat_runitor_laws
    : double_runitor_laws prod_double_cat_runitor_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_twosided_disp_cat_product.
    use dirprodeq ; cbn.
    - refine (_ @ !(runitor_square _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
    - refine (_ @ !(runitor_square _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  Definition prod_double_cat_runitor
    : double_cat_runitor prod_double_cat_hor_id prod_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact prod_double_cat_runitor_data.
    - exact prod_double_cat_runitor_laws.
  Defined.

  Definition prod_double_cat_associator_data
    : double_associator_data prod_double_cat_hor_comp.
  Proof.
    refine (λ w x y z f g h,
            (lassociator_h (pr1 f) (pr1 g) (pr1 h)
             ,,
             lassociator_h (pr2 f) (pr2 g) (pr2 h))
            ,, _).
    use is_isotwosided_disp_twosided_disp_cat_product.
    - refine (rassociator_h (pr1 f) (pr1 g) (pr1 h) ,, _ ,, _).
      + apply lassociator_rassociator_h.
      + apply rassociator_lassociator_h.
    - refine (rassociator_h (pr2 f) (pr2 g) (pr2 h) ,, _ ,, _).
      + apply lassociator_rassociator_h.
      + apply rassociator_lassociator_h.
  Defined.

  Proposition prod_double_cat_associator_laws
    : double_associator_laws prod_double_cat_associator_data.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_twosided_disp_cat_product.
    use dirprodeq ; cbn.
    - refine (_ @ !(lassociator_square _ _ _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
    - refine (_ @ !(lassociator_square _ _ _)).
      apply transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  Definition prod_double_cat_associator
    : double_cat_associator prod_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact prod_double_cat_associator_data.
    - exact prod_double_cat_associator_laws.
  Defined.

  (** * 3. The triangle and pentagon *)
  Proposition prod_double_cat_triangle
    : triangle_law
        prod_double_cat_lunitor
        prod_double_cat_runitor
        prod_double_cat_associator.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_twosided_disp_cat_product.
    use dirprodeq ; cbn.
    - refine (double_triangle _ _ @ _).
      apply transportb_disp_mor2_eq.
      apply idpath.
    - refine (double_triangle _ _ @ _).
      apply transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  Proposition prod_double_cat_pentagon
    : pentagon_law prod_double_cat_associator.
  Proof.
    intro ; intros ; cbn.
    rewrite transportb_twosided_disp_cat_product.
    use dirprodeq ; cbn.
    - refine (_ @ double_pentagon _ _ _ _).
      apply transportb_disp_mor2_eq.
      apply idpath.
    - refine (_ @ double_pentagon _ _ _ _).
      apply transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  (** * 4. The product of double categories *)
  Definition prod_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact (category_binproduct D₁ D₂).
    - exact (twosided_disp_cat_product (hor_mor D₁) (hor_mor D₂)).
    - exact prod_double_cat_hor_id.
    - exact prod_double_cat_hor_comp.
    - exact prod_double_cat_lunitor.
    - exact prod_double_cat_runitor.
    - exact prod_double_cat_associator.
    - exact prod_double_cat_triangle.
    - exact prod_double_cat_pentagon.
  Defined.

  Proposition transportf_prod_double_cat
              {x₁ x₂ y₁ y₂ : prod_double_cat}
              {v₁ v₁' : x₁ -->v y₁}
              (p : v₁ = v₁')
              {v₂ v₂' : x₂ -->v y₂}
              (q : v₂ = v₂')
              {h₁ : x₁ -->h x₂}
              {h₂ : y₁ -->h y₂}
              (s : square v₁ v₂ h₁ h₂)
    : transportf_square p q s
      =
      transportf_square (maponpaths pr1 p) (maponpaths pr1 q) (pr1 s)
      ,,
      transportf_square (maponpaths dirprod_pr2 p) (maponpaths dirprod_pr2 q) (pr2 s).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Definition transportb_prod_double_cat
             {x₁ x₂ y₁ y₂ : prod_double_cat}
             {v₁ v₁' : x₁ -->v y₁}
             (p : v₁' = v₁)
             {v₂ v₂' : x₂ -->v y₂}
             (q : v₂' = v₂)
             {h₁ : x₁ -->h x₂}
             {h₂ : y₁ -->h y₂}
             (s : square v₁ v₂ h₁ h₂)
    : transportb_square p q s
      =
      transportb_square (maponpaths pr1 p) (maponpaths pr1 q) (pr1 s)
      ,,
      transportb_square (maponpaths dirprod_pr2 p) (maponpaths dirprod_pr2 q) (pr2 s).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.
End ProdOfDoubleCat.

Definition prod_univalent_double_cat
           (D₁ D₂ : univalent_double_cat)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (prod_double_cat D₁ D₂).
  - split.
    + use is_univalent_category_binproduct.
      * apply univalent_category_is_univalent.
      * apply univalent_category_is_univalent.
    + use is_univalent_twosided_disp_cat_product.
      * apply is_univalent_twosided_disp_cat_hor_mor.
      * apply is_univalent_twosided_disp_cat_hor_mor.
Defined.

Definition make_prod_ob
           {D₁ D₂ : univalent_double_cat}
           (x : D₁)
           (y : D₂)
  : prod_univalent_double_cat D₁ D₂
  := x ,, y.

Definition make_prod_ver
           {D₁ D₂ : univalent_double_cat}
           {x y : D₁}
           (v : x -->v y)
           {x' y' : D₂}
           (v' : x' -->v y')
  : make_prod_ob x x' -->v make_prod_ob y y'
  := v ,, v'.

Definition make_prod_hor
           {D₁ D₂ : univalent_double_cat}
           {x y : D₁}
           (h : x -->h y)
           {x' y' : D₂}
           (h' : x' -->h y')
  : make_prod_ob x x' -->h make_prod_ob y y'
  := h ,, h'.

Definition make_prod_square
           {D₁ D₂ : univalent_double_cat}
           {x₁ x₂ y₁ y₂ : D₁}
           {v₁ : x₁ -->v y₁}
           {v₂ : x₂ -->v y₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s : square v₁ v₂ h₁ h₂)
           {x₁' x₂' y₁' y₂' : D₂}
           {v₁' : x₁' -->v y₁'}
           {v₂' : x₂' -->v y₂'}
           {h₁' : x₁' -->h x₂'}
           {h₂' : y₁' -->h y₂'}
           (s' : square v₁' v₂' h₁' h₂')
  : square
      (make_prod_ver v₁ v₁') (make_prod_ver v₂ v₂')
      (make_prod_hor h₁ h₁') (make_prod_hor h₂ h₂')
  := s ,, s'.

(** * 5. Projections *)
Section Projections.
  Context (D₁ D₂ : univalent_double_cat).

  Definition pr1_twosided_disp_functor_data
    : twosided_disp_functor_double_cat_data
        (prod_univalent_double_cat D₁ D₂)
        D₁
        (pr1_functor D₁ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, pr1 f).
    - exact (λ x₁ x₂ y₁ y₂ h k f g s, pr1 s).
  Defined.

  Proposition pr1_twosided_disp_functor_laws
    : twosided_disp_functor_double_cat_laws
        pr1_twosided_disp_functor_data.
  Proof.
    split.
    - intro ; intros.
      cbn -[id_v_square].
      rewrite transportb_square_id.
      apply idpath.
    - intro ; intros.
      cbn -[id_v_square].
      rewrite transportb_square_id.
      apply idpath.
  Qed.

  Definition pr1_twosided_disp_functor
    : twosided_disp_functor
        (pr1_functor D₁ D₂)
        (pr1_functor D₁ D₂)
        (hor_mor (prod_univalent_double_cat D₁ D₂))
        (hor_mor D₁).
  Proof.
    use (make_twosided_disp_functor_double_cat (prod_univalent_double_cat D₁ D₂)).
    - exact pr1_twosided_disp_functor_data.
    - exact pr1_twosided_disp_functor_laws.
  Defined.

  Definition prod_univalent_double_cat_pr1_hor_id
    : double_functor_hor_id
        pr1_twosided_disp_functor
        (hor_id_double_cat (prod_univalent_double_cat D₁ D₂))
        (hor_id_double_cat D₁).
  Proof.
    use (make_double_functor_hor_id_double_cat
           (C₁ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ _, id_v_square _).
    - abstract
        (intro ; intros ;
         cbn ;
         rewrite square_id_left_v ;
         rewrite square_id_right_v ;
         rewrite transportb_b_square ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Definition prod_univalent_double_cat_pr1_hor_comp
    : double_functor_hor_comp
        pr1_twosided_disp_functor
        (hor_comp_double_cat (prod_univalent_double_cat D₁ D₂))
        (hor_comp_double_cat D₁).
  Proof.
    use (make_double_functor_hor_comp_double_cat
           (C₁ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ x y z h k, id_v_square (pr1 h ·h pr1 k)).
    - abstract
        (intro ; intros ;
         cbn ;
         rewrite square_id_left_v ;
         rewrite square_id_right_v ;
         rewrite transportb_b_square ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Proposition prod_univalent_double_cat_pr1_lunitor
    : double_functor_lunitor
        (double_cat_double_lunitor (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_lunitor D₁)
        prod_univalent_double_cat_pr1_hor_id
        prod_univalent_double_cat_pr1_hor_comp.
  Proof.
    use make_double_functor_lunitor_double_cat.
    intros x y h ; cbn.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply (square_id_left_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite <- id_h_square_id.
    etrans.
    {
      apply maponpaths.
      apply (lunitor_square (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Proposition prod_univalent_double_cat_pr1_runitor
    : double_functor_runitor
        (double_cat_double_runitor (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_runitor D₁)
        prod_univalent_double_cat_pr1_hor_id
        prod_univalent_double_cat_pr1_hor_comp.
  Proof.
    use make_double_functor_runitor_double_cat.
    intros x y h ; cbn.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply (square_id_left_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite <- id_h_square_id.
    etrans.
    {
      apply maponpaths.
      apply (runitor_square (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Proposition prod_univalent_double_cat_pr1_associator
    : double_functor_associator
        (double_cat_double_associator (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_associator D₁)
        prod_univalent_double_cat_pr1_hor_comp.
  Proof.
    use make_double_functor_associator_double_cat.
    intros w x y z h₁ h₂ h₃ ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite <- comp_h_square_id.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (lassociator_square' (C := D₁)).
    }
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    rewrite <- comp_h_square_id.
    apply idpath.
  Qed.

  Definition prod_univalent_double_cat_pr1
    : lax_double_functor (prod_univalent_double_cat D₁ D₂) D₁.
  Proof.
    use make_lax_double_functor.
    - apply pr1_functor.
    - exact pr1_twosided_disp_functor.
    - exact prod_univalent_double_cat_pr1_hor_id.
    - exact prod_univalent_double_cat_pr1_hor_comp.
    - exact prod_univalent_double_cat_pr1_lunitor.
    - exact prod_univalent_double_cat_pr1_runitor.
    - exact prod_univalent_double_cat_pr1_associator.
  Defined.

  Definition pr2_twosided_disp_functor_data
    : twosided_disp_functor_double_cat_data
        (prod_univalent_double_cat D₁ D₂)
        D₂
        (pr2_functor D₁ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, pr2 f).
    - exact (λ x₁ x₂ y₁ y₂ h k f g s, pr2 s).
  Defined.

  Proposition pr2_twosided_disp_functor_laws
    : twosided_disp_functor_double_cat_laws
        pr2_twosided_disp_functor_data.
  Proof.
    split.
    - intro ; intros.
      cbn -[id_v_square].
      rewrite transportb_square_id.
      apply idpath.
    - intro ; intros.
      cbn -[id_v_square].
      rewrite transportb_square_id.
      apply idpath.
  Qed.

  Definition pr2_twosided_disp_functor
    : twosided_disp_functor
        (pr2_functor D₁ D₂)
        (pr2_functor D₁ D₂)
        (hor_mor (prod_univalent_double_cat D₁ D₂))
        (hor_mor D₂).
  Proof.
    use (make_twosided_disp_functor_double_cat (prod_univalent_double_cat D₁ D₂)).
    - exact pr2_twosided_disp_functor_data.
    - exact pr2_twosided_disp_functor_laws.
  Defined.

  Definition prod_univalent_double_cat_pr2_hor_id
    : double_functor_hor_id
        pr2_twosided_disp_functor
        (hor_id_double_cat (prod_univalent_double_cat D₁ D₂))
        (hor_id_double_cat D₂).
  Proof.
    use (make_double_functor_hor_id_double_cat
           (C₁ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ _, id_v_square _).
    - abstract
        (intro ; intros ;
         cbn ;
         rewrite square_id_left_v ;
         rewrite square_id_right_v ;
         rewrite transportb_b_square ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Definition prod_univalent_double_cat_pr2_hor_comp
    : double_functor_hor_comp
        pr2_twosided_disp_functor
        (hor_comp_double_cat (prod_univalent_double_cat D₁ D₂))
        (hor_comp_double_cat D₂).
  Proof.
    use (make_double_functor_hor_comp_double_cat
           (C₁ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ x y z h k, id_v_square (pr2 h ·h pr2 k)).
    - abstract
        (intro ; intros ;
         cbn ;
         rewrite square_id_left_v ;
         rewrite square_id_right_v ;
         rewrite transportb_b_square ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Proposition prod_univalent_double_cat_pr2_lunitor
    : double_functor_lunitor
        (double_cat_double_lunitor (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_lunitor D₂)
        prod_univalent_double_cat_pr2_hor_id
        prod_univalent_double_cat_pr2_hor_comp.
  Proof.
    use make_double_functor_lunitor_double_cat.
    intros x y h ; cbn.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply (square_id_left_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite <- id_h_square_id.
    etrans.
    {
      apply maponpaths.
      apply (lunitor_square (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Proposition prod_univalent_double_cat_pr2_runitor
    : double_functor_runitor
        (double_cat_double_runitor (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_runitor D₂)
        prod_univalent_double_cat_pr2_hor_id
        prod_univalent_double_cat_pr2_hor_comp.
  Proof.
    use make_double_functor_runitor_double_cat.
    intros x y h ; cbn.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply (square_id_left_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite <- id_h_square_id.
    etrans.
    {
      apply maponpaths.
      apply (runitor_square (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    apply transportf_square_id.
  Qed.

  Proposition prod_univalent_double_cat_pr2_associator
    : double_functor_associator
        (double_cat_double_associator (prod_univalent_double_cat D₁ D₂))
        (double_cat_double_associator D₂)
        prod_univalent_double_cat_pr2_hor_comp.
  Proof.
    use make_double_functor_associator_double_cat.
    intros w x y z h₁ h₂ h₃ ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite <- comp_h_square_id.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (lassociator_square' (C := D₂)).
    }
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    rewrite <- comp_h_square_id.
    apply idpath.
  Qed.

  Definition prod_univalent_double_cat_pr2
    : lax_double_functor (prod_univalent_double_cat D₁ D₂) D₂.
  Proof.
    use make_lax_double_functor.
    - apply pr2_functor.
    - exact pr2_twosided_disp_functor.
    - exact prod_univalent_double_cat_pr2_hor_id.
    - exact prod_univalent_double_cat_pr2_hor_comp.
    - exact prod_univalent_double_cat_pr2_lunitor.
    - exact prod_univalent_double_cat_pr2_runitor.
    - exact prod_univalent_double_cat_pr2_associator.
  Defined.
End Projections.

(** * 6. Pairing *)
Section Pairing.
  Context {C D₁ D₂ : univalent_double_cat}
          (F : lax_double_functor C D₁)
          (G : lax_double_functor C D₂).

  Let FG : C ⟶ category_binproduct D₁ D₂ := bindelta_pair_functor F G.

  Definition pair_twosided_disp_functor_data
    : twosided_disp_functor_double_cat_data
        C (prod_univalent_double_cat D₁ D₂)
        FG.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y h, #h F h ,, #h G h).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g s, #s F s ,, #s G s).
  Defined.

  Proposition pair_twosided_disp_functor_laws
    : twosided_disp_functor_double_cat_laws
        pair_twosided_disp_functor_data.
  Proof.
    split.
    - intros x y h.
      use dirprodeq ; cbn -[id_v_square].
      + refine (lax_double_functor_id_square F _ @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (transportb_prod_double_cat D₁ D₂ _ _ (id_v_square _)).
        }
        use transportb_square_eq.
        apply idpath.
      + refine (lax_double_functor_id_square G _ @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (transportb_prod_double_cat D₁ D₂ _ _ (id_v_square _)).
        }
        use transportb_square_eq.
        apply idpath.
    - intro ; intros.
      use dirprodeq ; cbn -[comp_v_square].
      + refine (lax_double_functor_comp_v_square F _ _ @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (transportb_prod_double_cat D₁ D₂ _ _ (_ ⋆v _)).
        }
        use transportb_square_eq.
        apply idpath.
      + refine (lax_double_functor_comp_v_square G _ _ @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (transportb_prod_double_cat D₁ D₂ _ _ (_ ⋆v _)).
        }
        use transportb_square_eq.
        apply idpath.
  Qed.

  Definition pair_twosided_disp_functor
    : twosided_disp_functor
        FG FG
        (hor_mor C)
        (hor_mor (prod_univalent_double_cat D₁ D₂)).
  Proof.
    use (make_twosided_disp_functor_double_cat C (prod_univalent_double_cat D₁ D₂)).
    - exact pair_twosided_disp_functor_data.
    - exact pair_twosided_disp_functor_laws.
  Defined.

  Definition pair_lax_double_functor_hor_id
    : double_functor_hor_id
        pair_twosided_disp_functor
        (hor_id_double_cat C)
        (hor_id_double_cat (prod_univalent_double_cat D₁ D₂)).
  Proof.
    use (make_double_functor_hor_id_double_cat
           (C₂ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ x, lax_double_functor_id_h F _ ,, lax_double_functor_id_h G _).
    - abstract
        (intros x y v ;
         refine (_ @ !(transportb_prod_double_cat D₁ D₂ _ _ _)) ;
         use dirprodeq ; cbn ;
         refine (lax_double_functor_id_h_mor _ _ @ _) ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Definition pair_lax_double_functor_hor_comp
    : double_functor_hor_comp
        pair_twosided_disp_functor
        (hor_comp_double_cat C)
        (hor_comp_double_cat (prod_univalent_double_cat D₁ D₂)).
  Proof.
    use (make_double_functor_hor_comp_double_cat
           (C₂ := prod_univalent_double_cat D₁ D₂)).
    - exact (λ x y z h k,
             lax_double_functor_comp_h F _ _
             ,,
             lax_double_functor_comp_h G _ _).
    - abstract
        (intros ;
         refine (_ @ !(transportb_prod_double_cat D₁ D₂ _ _ _)) ;
         use dirprodeq ;
         refine (lax_double_functor_comp_h_mor _ _ _ @ _) ;
         use transportb_square_eq ;
         apply idpath).
  Defined.

  Definition pair_lax_double_functor_lunitor
    : double_functor_lunitor
        (double_cat_double_lunitor C)
        (double_cat_double_lunitor (prod_univalent_double_cat D₁ D₂))
        pair_lax_double_functor_hor_id
        pair_lax_double_functor_hor_comp.
  Proof.
    use make_double_functor_lunitor_double_cat.
    intros x y h.
    refine (_ @ !(transportf_prod_double_cat D₁ D₂ _ _ _)).
    use dirprodeq.
    - refine (lax_double_functor_lunitor_h _ _ @ _).
      use transportf_square_eq.
      apply idpath.
    - refine (lax_double_functor_lunitor_h _ _ @ _).
      use transportf_square_eq.
      apply idpath.
  Qed.

  Definition pair_lax_double_functor_runitor
    : double_functor_runitor
        (double_cat_double_runitor C)
        (double_cat_double_runitor (prod_univalent_double_cat D₁ D₂))
        pair_lax_double_functor_hor_id
        pair_lax_double_functor_hor_comp.
  Proof.
    use make_double_functor_runitor_double_cat.
    intros x y h.
    refine (_ @ !(transportf_prod_double_cat D₁ D₂ _ _ _)).
    use dirprodeq.
    - refine (lax_double_functor_runitor_h _ _ @ _).
      use transportf_square_eq.
      apply idpath.
    - refine (lax_double_functor_runitor_h _ _ @ _).
      use transportf_square_eq.
      apply idpath.
  Qed.

  Definition pair_lax_double_functor_associator
    : double_functor_associator
        (double_cat_double_associator C)
        (double_cat_double_associator (prod_univalent_double_cat D₁ D₂))
        pair_lax_double_functor_hor_comp.
  Proof.
    use make_double_functor_associator_double_cat.
    intro ; intros.
    refine (_ @ !(transportf_prod_double_cat D₁ D₂ _ _ _)).
    use dirprodeq.
    - refine (lax_double_functor_lassociator_h _ _ _ _ @ _).
      use transportf_square_eq.
      apply idpath.
    - refine (lax_double_functor_lassociator_h _ _ _ _ @ _).
      use transportf_square_eq.
      apply idpath.
  Qed.

  Definition pair_lax_double_functor
    : lax_double_functor C (prod_univalent_double_cat D₁ D₂).
  Proof.
    use make_lax_double_functor.
    - exact FG.
    - exact pair_twosided_disp_functor.
    - exact pair_lax_double_functor_hor_id.
    - exact pair_lax_double_functor_hor_comp.
    - exact pair_lax_double_functor_lunitor.
    - exact pair_lax_double_functor_runitor.
    - exact pair_lax_double_functor_associator.
  Defined.

  Definition pair_lax_double_functor_pr1_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_double_cat_data F F (bindelta_pair_pr1 F G)
    := λ x y h, id_v_square (#h F h).

  Arguments pair_lax_double_functor_pr1_twosided_disp_nat_trans_data /.

  Proposition pair_lax_double_functor_pr1_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_double_cat_laws
        pair_lax_double_functor_pr1_twosided_disp_nat_trans_data.
  Proof.
    intro ; intros ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₁)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₁)).
    }
    rewrite transportb_b_square.
    use transportb_square_eq.
    apply idpath.
  Qed.

  Definition pair_lax_double_functor_pr1_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (bindelta_pair_pr1 F G) (bindelta_pair_pr1 F G)
        (lax_double_functor_hor_mor
           (pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂))
        (lax_double_functor_hor_mor F).
  Proof.
    use make_twosided_disp_nat_trans_double_cat.
    - exact pair_lax_double_functor_pr1_twosided_disp_nat_trans_data.
    - exact pair_lax_double_functor_pr1_twosided_disp_nat_trans_laws.
  Defined.

  Proposition pair_lax_double_functor_pr1_hor_id
    : double_nat_trans_hor_id
        pair_lax_double_functor_pr1_twosided_disp_nat_trans
        (lax_double_functor_hor_id
           (pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂))
        (lax_double_functor_hor_id F).
  Proof.
    use (make_double_nat_trans_hor_id
           (F := pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂)).
    intro x ; cbn ; unfold bindelta_pair_pr1_data ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ (id_v_square _ ⋆v lax_double_functor_id_h F x)).
    }
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₁)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (id_h_square_id (C := D₁)).
      }
      apply (square_id_left_v (C := D₁)).
    }
    unfold transportb_square.
    rewrite !transportf_f_square.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Proposition pair_lax_double_functor_pr1_hor_comp
    : double_nat_trans_hor_comp
        pair_lax_double_functor_pr1_twosided_disp_nat_trans
        (lax_double_functor_hor_comp
           (pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂))
        (lax_double_functor_hor_comp F).
  Proof.
    use (make_double_nat_trans_hor_comp
           (F := pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂)).
    intros x y z h k ; cbn ; unfold bindelta_pair_pr1_data ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₁)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₁)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (comp_h_square_id (C := D₁)).
      }
      apply (square_id_left_v (C := D₁)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ _).
    }
    rewrite !transportf_f_square.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition pair_lax_double_functor_pr1
    : double_transformation
        (pair_lax_double_functor · prod_univalent_double_cat_pr1 D₁ D₂)
        F.
  Proof.
    use make_double_transformation.
    - apply bindelta_pair_pr1.
    - exact pair_lax_double_functor_pr1_twosided_disp_nat_trans.
    - exact pair_lax_double_functor_pr1_hor_id.
    - exact pair_lax_double_functor_pr1_hor_comp.
  Defined.

  Definition is_invertible_2cell_pair_lax_double_functor_pr1
    : is_invertible_2cell pair_lax_double_functor_pr1.
  Proof.
    use is_invertible_2cell_double_transformation_unfolded.
    - intro x.
      apply identity_is_z_iso.
    - intros x y f.
      apply id_is_iso_twosided_disp.
  Defined.

  Definition pair_lax_double_functor_pr2_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_double_cat_data G G (bindelta_pair_pr2 F G)
    := λ x y h, id_v_square (#h G h).

  Arguments pair_lax_double_functor_pr2_twosided_disp_nat_trans_data /.

  Proposition pair_lax_double_functor_pr2_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_double_cat_laws
        pair_lax_double_functor_pr2_twosided_disp_nat_trans_data.
  Proof.
    intro ; intros ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₂)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₂)).
    }
    rewrite transportb_b_square.
    use transportb_square_eq.
    apply idpath.
  Qed.

  Definition pair_lax_double_functor_pr2_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (bindelta_pair_pr2 F G) (bindelta_pair_pr2 F G)
        (lax_double_functor_hor_mor
           (pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂))
        (lax_double_functor_hor_mor G).
  Proof.
    use make_twosided_disp_nat_trans_double_cat.
    - exact pair_lax_double_functor_pr2_twosided_disp_nat_trans_data.
    - exact pair_lax_double_functor_pr2_twosided_disp_nat_trans_laws.
  Defined.

  Proposition pair_lax_double_functor_pr2_hor_id
    : double_nat_trans_hor_id
        pair_lax_double_functor_pr2_twosided_disp_nat_trans
        (lax_double_functor_hor_id
           (pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂))
        (lax_double_functor_hor_id G).
  Proof.
    use (make_double_nat_trans_hor_id
           (F := pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂)).
    intro x ; cbn ; unfold bindelta_pair_pr1_data ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ (id_v_square _ ⋆v lax_double_functor_id_h G x)).
    }
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₂)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (id_h_square_id (C := D₂)).
      }
      apply (square_id_left_v (C := D₂)).
    }
    unfold transportb_square.
    rewrite !transportf_f_square.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Proposition pair_lax_double_functor_pr2_hor_comp
    : double_nat_trans_hor_comp
        pair_lax_double_functor_pr2_twosided_disp_nat_trans
        (lax_double_functor_hor_comp
           (pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂))
        (lax_double_functor_hor_comp G).
  Proof.
    use (make_double_nat_trans_hor_comp
           (F := pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂)).
    intros x y z h k ; cbn ; unfold bindelta_pair_pr1_data ; cbn.
    etrans.
    {
      apply (square_id_right_v (C := D₂)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      apply (square_id_left_v (C := D₂)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (comp_h_square_id (C := D₂)).
      }
      apply (square_id_left_v (C := D₂)).
    }
    unfold transportb_square.
    etrans.
    {
      exact (transportf_f_square _ _ _ _ _).
    }
    rewrite !transportf_f_square.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition pair_lax_double_functor_pr2
    : double_transformation
        (pair_lax_double_functor · prod_univalent_double_cat_pr2 D₁ D₂)
        G.
  Proof.
    use make_double_transformation.
    - apply bindelta_pair_pr2.
    - exact pair_lax_double_functor_pr2_twosided_disp_nat_trans.
    - exact pair_lax_double_functor_pr2_hor_id.
    - exact pair_lax_double_functor_pr2_hor_comp.
  Defined.

  Definition is_invertible_2cell_pair_lax_double_functor_pr2
    : is_invertible_2cell pair_lax_double_functor_pr2.
  Proof.
    use is_invertible_2cell_double_transformation_unfolded.
    - intro x.
      apply identity_is_z_iso.
    - intros x y f.
      apply id_is_iso_twosided_disp.
  Defined.
End Pairing.

(** * 7. Pairing of double transformations *)
Section PairTransformation.
  Context {C D₁ D₂ : univalent_double_cat}
          {F G : lax_double_functor C (prod_univalent_double_cat D₁ D₂)}
          (τ : double_transformation
                 (F · prod_univalent_double_cat_pr1 D₁ D₂)
                 (G · prod_univalent_double_cat_pr1 D₁ D₂))
          (θ : double_transformation
                 (F · prod_univalent_double_cat_pr2 D₁ D₂)
                 (G · prod_univalent_double_cat_pr2 D₁ D₂)).

  Definition pair_double_transformation_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_double_cat_data F G (prod_nat_trans τ θ)
    := λ x y h,
       make_prod_square
         (double_transformation_hor_mor τ h)
         (double_transformation_hor_mor θ h).

  Proposition pair_double_transformation_twosided_disp_nat_laws
    : twosided_disp_nat_trans_double_cat_laws
        pair_double_transformation_twosided_disp_nat_trans_data.
  Proof.
    intro ; intros ; cbn -[prod_univalent_double_cat bicat_of_double_cats].
    refine (_ @ !(transportb_prod_double_cat _ _ _ _ _)).
    use dirprodeq.
    - refine (double_transformation_square τ s @ _).
      use transportb_square_eq.
      apply idpath.
    - refine (double_transformation_square θ s @ _).
      use transportb_square_eq.
      apply idpath.
  Qed.

  Definition pair_double_transformation_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (prod_nat_trans τ θ) (prod_nat_trans τ θ)
        (lax_double_functor_hor_mor F)
        (lax_double_functor_hor_mor G).
  Proof.
    use (make_twosided_disp_nat_trans_double_cat (F := F) (G := G)).
    - exact pair_double_transformation_twosided_disp_nat_trans_data.
    - exact pair_double_transformation_twosided_disp_nat_laws.
  Defined.

  Proposition pair_double_transformation_hor_id
    : double_nat_trans_hor_id
        pair_double_transformation_twosided_disp_nat_trans
        (lax_double_functor_hor_id F)
        (lax_double_functor_hor_id G).
  Proof.
    use (make_double_nat_trans_hor_id (F := F) (G := G)).
    cbn -[prod_univalent_double_cat bicat_of_double_cats].
    intro x.
    refine (_ @ !(transportb_prod_double_cat _ _ _ _ _)).
    use dirprodeq ; cbn -[prod_univalent_double_cat bicat_of_double_cats].
    - refine (_ @ double_transformation_id_h τ x @ _).
      + refine (maponpaths (λ z, z ⋆v _) _).
        refine (!_).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₁)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₁)).
        }
        apply transportf_square_id.
      + use transportb_square_eq.
        refine (maponpaths (λ z, _ ⋆v z) _).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₁)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₁)).
        }
        apply transportf_square_id.
    - refine (_ @ double_transformation_id_h θ x @ _).
      + refine (maponpaths (λ z, z ⋆v _) _).
        refine (!_).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₂)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₂)).
        }
        apply transportf_square_id.
      + use transportb_square_eq.
        refine (maponpaths (λ z, _ ⋆v z) _).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₂)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₂)).
        }
        apply transportf_square_id.
  Qed.

  Proposition pair_double_transformation_hor_comp
    : double_nat_trans_hor_comp
        pair_double_transformation_twosided_disp_nat_trans
        (lax_double_functor_hor_comp F)
        (lax_double_functor_hor_comp G).
  Proof.
    use (make_double_nat_trans_hor_comp (F := F) (G := G)).
    cbn -[prod_univalent_double_cat bicat_of_double_cats].
    intros x y z h k.
    refine (_ @ !(transportb_prod_double_cat _ _ _ _ _)).
    use dirprodeq ; cbn -[prod_univalent_double_cat bicat_of_double_cats].
    - refine (_ @ double_transformation_comp_h τ h k @ _).
      + refine (maponpaths (λ z, z ⋆v _) _).
        refine (!_).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₁)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₁)).
        }
        apply transportf_square_id.
      + use transportb_square_eq.
        refine (maponpaths (λ z, _ ⋆v z) _).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₁)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₁)).
        }
        apply transportf_square_id.
    - refine (_ @ double_transformation_comp_h θ h k @ _).
      + refine (maponpaths (λ z, z ⋆v _) _).
        refine (!_).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₂)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₂)).
        }
        apply transportf_square_id.
      + use transportb_square_eq.
        refine (maponpaths (λ z, _ ⋆v z) _).
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (square_id_left_v (C := D₂)).
        }
        unfold transportb_square.
        etrans.
        {
          apply (transportf_f_square (C := D₂)).
        }
        apply transportf_square_id.
  Qed.

  Definition pair_double_transformation
    : double_transformation F G.
  Proof.
    use make_double_transformation.
    - exact (prod_nat_trans τ θ).
    - exact pair_double_transformation_twosided_disp_nat_trans.
    - exact pair_double_transformation_hor_id.
    - exact pair_double_transformation_hor_comp.
  Defined.

  Proposition pair_double_transformation_pr1
    : pair_double_transformation ▹ prod_univalent_double_cat_pr1 D₁ D₂
      =
      τ.
  Proof.
    use double_transformation_eq.
    - intro x.
      apply idpath.
    - intros x y f.
      apply idpath.
  Qed.

  Proposition pair_double_transformation_pr2
    : pair_double_transformation ▹ prod_univalent_double_cat_pr2 D₁ D₂
      =
      θ.
  Proof.
    use double_transformation_eq.
    - intro x.
      apply idpath.
    - intros x y f.
      apply idpath.
  Qed.

  Proposition pair_double_transformation_unique
    : isaprop
        (∑ (γ : F ==> G),
         (γ ▹ prod_univalent_double_cat_pr1 D₁ D₂ = τ)
         ×
         (γ ▹ prod_univalent_double_cat_pr2 D₁ D₂ = θ)).
  Proof.
    use invproofirrelevance.
    intros γ₁ γ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    induction γ₁ as [ γ₁ [ p₁ q₁ ]].
    induction γ₂ as [ γ₂ [ p₂ q₂ ]].
    cbn.
    pose (p := p₁ @ !p₂).
    pose (q := q₁ @ !q₂).
    use double_transformation_eq.
    - intro x.
      use dirprodeq.
      + exact (double_transformation_eq_ob p x).
      + exact (double_transformation_eq_ob q x).
    - intros x y h.
      refine (_ @ !(transportb_prod_double_cat _ _ _ _ _)).
      use dirprodeq.
      + refine (double_transformation_eq_hor_mor p h @ _).
        use transportb_square_eq.
        apply idpath.
      + refine (double_transformation_eq_hor_mor q h @ _).
        use transportb_square_eq.
        apply idpath.
  Qed.
End PairTransformation.

(** * 8. Products of double categories *)
Section BinProduct.
  Context (D₁ D₂ : bicat_of_double_cats).

  Definition double_cat_binprod_cone
    : binprod_cone D₁ D₂.
  Proof.
    use make_binprod_cone.
    - exact (prod_univalent_double_cat D₁ D₂).
    - exact (prod_univalent_double_cat_pr1 D₁ D₂).
    - exact (prod_univalent_double_cat_pr2 D₁ D₂).
  Defined.

  Definition double_cat_binprod_ump_1
    : binprod_ump_1 double_cat_binprod_cone.
  Proof.
    intros q.
    use make_binprod_1cell.
    - exact (pair_lax_double_functor
               (binprod_cone_pr1 q)
               (binprod_cone_pr2 q)).
    - use make_invertible_2cell.
      + apply pair_lax_double_functor_pr1.
      + apply is_invertible_2cell_pair_lax_double_functor_pr1.
    - use make_invertible_2cell.
      + apply pair_lax_double_functor_pr2.
      + apply is_invertible_2cell_pair_lax_double_functor_pr2.
  Defined.

  Definition double_cat_binprod_ump_2
    : binprod_ump_2 double_cat_binprod_cone.
  Proof.
    intros C F G τ θ.
    use iscontraprop1.
    - exact (pair_double_transformation_unique τ θ).
    - simple refine (_ ,, _ ,, _).
      + exact (pair_double_transformation τ θ).
      + exact (pair_double_transformation_pr1 τ θ).
      + exact (pair_double_transformation_pr2 τ θ).
  Defined.

  Definition double_cat_binprod_ump
    : has_binprod_ump double_cat_binprod_cone.
  Proof.
    split.
    - exact double_cat_binprod_ump_1.
    - exact double_cat_binprod_ump_2.
  Defined.
End BinProduct.

Definition has_binprod_bicat_of_double_cat
  : has_binprod bicat_of_double_cats
  := λ D₁ D₂,
     double_cat_binprod_cone D₁ D₂
     ,,
     double_cat_binprod_ump D₁ D₂.
