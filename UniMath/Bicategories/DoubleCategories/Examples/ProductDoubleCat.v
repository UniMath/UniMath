(************************************************************************************

 The product of double categories

 In this file, we define the product of double categories. Given double categories
 `D₁` and `D₂`, the product of `D₁` and `D₂` is defined as follows:
 - Objects: pairs of objects in `D₁` and `D₂`
 - Vertical morphisms: pairs of vertical morphisms in `D₁` and `D₂`
 - Horizontal morphisms: pairs of horizontal morphisms in `D₁` and `D₂`
 - Squares: pairs of squares in `D₁` and `D₂`
 The operations are defined coordinate-wise.

 Contents
 1. Horizontal identity and composition
 2. Unitors and associator
 3. The triangle and pentagon
 4. The product of double categories

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
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ProdOfTwosidedDispCat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.

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
