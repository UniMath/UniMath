(**********************************************************************************

 The unit double category

 In this file, we define the unit double category. Its objects, vertical morphisms,
 horizontal morphisms, and squares are all inhabitants of the unit type.

 Contents
 1. Horizontal operations of the unit double category
 2. The unit double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.

Local Open Scope cat.

(** * 1. Horizontal operations of the unit double category *)
Definition unit_double_cat_hor_id_data
  : hor_id_data (constant_twosided_disp_cat unit_category unit_category unit_category).
Proof.
  use make_hor_id_data.
  - exact (λ _, tt).
  - exact (λ _ _ _, idpath _).
Defined.

Proposition unit_double_cat_hor_id_laws
  : hor_id_laws unit_double_cat_hor_id_data.
Proof.
  split.
  - intros.
    apply isapropunit.
  - intros.
    apply isapropunit.
Qed.

Definition unit_double_cat_hor_id
  : hor_id (constant_twosided_disp_cat unit_category unit_category unit_category).
Proof.
  use make_hor_id.
  - exact unit_double_cat_hor_id_data.
  - exact unit_double_cat_hor_id_laws.
Defined.

Definition unit_double_cat_hor_comp_data
  : hor_comp_data (constant_twosided_disp_cat unit_category unit_category unit_category).
Proof.
  use make_hor_comp_data.
  - exact (λ _ _ _ _ _, tt).
  - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, idpath _).
Defined.

Proposition unit_double_cat_hor_comp_laws
  : hor_comp_laws unit_double_cat_hor_comp_data.
Proof.
  split.
  - intros.
    apply isapropunit.
  - intros.
    apply isapropunit.
Qed.

Definition unit_double_cat_hor_comp
  : hor_comp (constant_twosided_disp_cat unit_category unit_category unit_category).
Proof.
  use make_hor_comp.
  - exact unit_double_cat_hor_comp_data.
  - exact unit_double_cat_hor_comp_laws.
Defined.

Definition unit_double_lunitor
  : double_cat_lunitor unit_double_cat_hor_id unit_double_cat_hor_comp.
Proof.
  use make_double_lunitor.
  - intros x y f.
    use make_iso_twosided_disp.
    + apply isapropunit.
    + use to_is_twosided_disp_cat_iso_constant.
      apply path_groupoid.
  - intro ; intros.
    apply isapropunit.
Qed.

Definition unit_double_runitor
  : double_cat_runitor unit_double_cat_hor_id unit_double_cat_hor_comp.
Proof.
  use make_double_runitor.
  - intros x y f.
    use make_iso_twosided_disp.
    + apply isapropunit.
    + use to_is_twosided_disp_cat_iso_constant.
      apply path_groupoid.
  - intro ; intros.
    apply isapropunit.
Qed.

Definition unit_double_associator
  : double_cat_associator unit_double_cat_hor_comp.
Proof.
  use make_double_associator.
  - intro ; intros.
    use make_iso_twosided_disp.
    + apply isapropunit.
    + use to_is_twosided_disp_cat_iso_constant.
      apply path_groupoid.
  - intro ; intros.
    apply isapropunit.
Qed.

(** * 2. The unit double category *)
Definition unit_double_cat
  : double_cat.
Proof.
  use make_double_cat.
  - exact unit_category.
  - exact (constant_twosided_disp_cat unit_category unit_category unit_category).
  - exact unit_double_cat_hor_id.
  - exact unit_double_cat_hor_comp.
  - exact unit_double_lunitor.
  - exact unit_double_runitor.
  - exact unit_double_associator.
  - abstract (intro ; intros ; apply isasetunit).
  - abstract (intro ; intros ; apply isasetunit).
Defined.

Definition unit_univalent_double_cat
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact unit_double_cat.
  - split.
    + apply univalent_category_is_univalent.
    + apply is_univalent_constant_twosided_disp_cat.
      apply univalent_category_is_univalent.
Defined.
