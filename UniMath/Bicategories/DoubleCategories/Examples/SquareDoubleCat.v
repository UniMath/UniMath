(**********************************************************************************

 The square double category of a category

 In this file, we construct a double category from any category `C`. This double
 category is called the square double category. The objects in this double category
 are objects in `C`, horizontal and vertical morphisms in this double category are
 morphisms in `C`, and the squares in this double category are commutative squares
 in `C`. To define this double category, we use the 2-sided displayed category of
 arrows. The operations on horizontal morphisms are inherited from `C`.

 Contents
 1. Horizontal operations
 2. The square double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Arrow.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.

Local Open Scope cat.

(**
 1. Horizontal operations
 *)
Section ArrowDoubleCategory.
  Context (C : category).

  Definition hor_id_data_arrow_twosided_disp_cat
    : hor_id_data (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id_data ; cbn.
    - exact (λ x, identity x).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Proposition hor_id_laws_arrow_twosided_disp_cat
    : hor_id_laws hor_id_data_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_id_arrow_twosided_disp_cat
    : hor_id (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id.
    - exact hor_id_data_arrow_twosided_disp_cat.
    - exact hor_id_laws_arrow_twosided_disp_cat.
  Defined.

  Definition hor_comp_data_arrow_twosided_disp_cat
    : hor_comp_data (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f · g).
    - abstract
        (intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn in * ;
         rewrite !assoc ;
         rewrite s₁ ;
         rewrite !assoc' ;
         rewrite s₂ ;
         apply idpath).
  Defined.

  Definition hor_comp_laws_arrow_twosided_disp_cat
    : hor_comp_laws hor_comp_data_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_comp_arrow_twosided_disp_cat
    : hor_comp (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp.
    - exact hor_comp_data_arrow_twosided_disp_cat.
    - exact hor_comp_laws_arrow_twosided_disp_cat.
  Defined.

  Definition double_cat_lunitor_arrow_twosided_disp_cat
    : double_cat_lunitor
        hor_id_arrow_twosided_disp_cat
        hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_lunitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_runitor_arrow_twosided_disp_cat
    : double_cat_runitor
        hor_id_arrow_twosided_disp_cat
        hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_runitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_associator_arrow_twosided_disp_cat
    : double_cat_associator hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_associator.
    - intros w x y z h₁ h₂ h₃ ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right, !assoc' ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Proposition triangle_law_arrow_twosided_disp_cat
    : triangle_law
        double_cat_lunitor_arrow_twosided_disp_cat
        double_cat_runitor_arrow_twosided_disp_cat
        double_cat_associator_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    apply homset_property.
  Qed.

  Proposition pentagon_law_arrow_twosided_disp_cat
    : pentagon_law double_cat_associator_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    apply homset_property.
  Qed.
End ArrowDoubleCategory.

(**
 2. The square double category
 *)
Definition square_double_cat
           (C : univalent_category)
  : double_cat.
Proof.
  use make_double_cat.
  - exact C.
  - exact (arrow_twosided_disp_cat C).
  - exact (hor_id_arrow_twosided_disp_cat C).
  - exact (hor_comp_arrow_twosided_disp_cat C).
  - exact (double_cat_lunitor_arrow_twosided_disp_cat C).
  - exact (double_cat_runitor_arrow_twosided_disp_cat C).
  - exact (double_cat_associator_arrow_twosided_disp_cat C).
  - exact (triangle_law_arrow_twosided_disp_cat C).
  - exact (pentagon_law_arrow_twosided_disp_cat C).
  - apply univalent_category_is_univalent.
  - apply is_univalent_arrow_twosided_disp_cat.
Defined.
