(**********************************************************************************

 The unit double category

 In this file, we define the unit double category. Its objects, vertical morphisms,
 horizontal morphisms, and squares are all inhabitants of the unit type. We also
 verify that it is a terminal object.

 Contents
 1. Horizontal operations of the unit double category
 2. The unit double category
 3. Functors to the unit double category
 4. Transformations to the unit double category
 5. The unit double category is a terminal object

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
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.Basics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleTransformation.

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

(** * 3. Functors to the unit double category *)
Section FunctorToUnitDoubleCat.
  Context (C : univalent_double_cat).

  Definition twosided_disp_functor_to_unit_double_cat_data
    : twosided_disp_functor_data
        (functor_to_unit C) (functor_to_unit C)
        (hor_mor C)
        (hor_mor unit_univalent_double_cat).
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _, idpath _).
  Defined.

  Proposition twosided_disp_functor_to_unit_double_cat_laws
    : twosided_disp_functor_laws
        _ _ _ _
        twosided_disp_functor_to_unit_double_cat_data.
  Proof.
    split ; intro ; intros ; apply isasetunit.
  Qed.

  Definition twosided_disp_functor_to_unit_double_cat
    : twosided_disp_functor
        (functor_to_unit C) (functor_to_unit C)
        (hor_mor C)
        (hor_mor unit_univalent_double_cat).
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_functor_to_unit_double_cat_data.
    - exact twosided_disp_functor_to_unit_double_cat_laws.
  Defined.

  Definition lax_double_functor_to_unit_double_cat_hor_id
    : double_functor_hor_id
        twosided_disp_functor_to_unit_double_cat
        (hor_id_double_cat C)
        (hor_id_double_cat unit_univalent_double_cat).
  Proof.
    use make_double_functor_hor_id.
    - intro x ; cbn.
      apply idpath.
    - abstract
        (intro ; intros ; cbn ;
         apply isasetunit).
  Defined.

  Definition lax_double_functor_to_unit_double_cat_hor_comp
    : double_functor_hor_comp
        twosided_disp_functor_to_unit_double_cat
        (hor_comp_double_cat C)
        (hor_comp_double_cat unit_univalent_double_cat).
  Proof.
    use make_double_functor_hor_comp.
    - intro ; intros ; cbn.
      apply idpath.
    - abstract
        (intro ; intros ; cbn ;
         apply isasetunit).
  Defined.

  Definition lax_double_functor_to_unit_double_cat
    : lax_double_functor C unit_univalent_double_cat.
  Proof.
    use make_lax_double_functor.
    - apply functor_to_unit.
    - exact twosided_disp_functor_to_unit_double_cat.
    - exact lax_double_functor_to_unit_double_cat_hor_id.
    - exact lax_double_functor_to_unit_double_cat_hor_comp.
    - abstract
        (intro ; intros ;
         apply isasetunit).
    - abstract
        (intro ; intros ;
         apply isasetunit).
    - abstract
        (intro ; intros ;
         apply isasetunit).
  Defined.
End FunctorToUnitDoubleCat.

(** * 4. Transformations to the unit double category *)
Section NatTransToUnitDoubleCat.
  Context {C : univalent_double_cat}
          (F G : lax_double_functor C unit_univalent_double_cat).

  Definition twosided_disp_nat_trans_to_unit_double_cat
    : twosided_disp_nat_trans
        (unit_category_nat_trans F G) (unit_category_nat_trans F G)
        (lax_double_functor_hor_mor F)
        (lax_double_functor_hor_mor G).
  Proof.
    simple refine (_ ,, _).
    - intro ; intros.
      apply isapropunit.
    - intro ; intros.
      apply isasetunit.
  Qed.

  Definition double_transformation_to_unit_double_cat
    : double_transformation F G.
  Proof.
    use make_double_transformation.
    - apply unit_category_nat_trans.
    - exact twosided_disp_nat_trans_to_unit_double_cat.
    - abstract
        (intro ; intros ;
         apply isasetunit).
    - abstract
        (intro ; intros ;
         apply isasetunit).
  Defined.
End NatTransToUnitDoubleCat.

Definition double_transformation_to_unit_double_cat_eq
           {C : univalent_double_cat}
           {F G : lax_double_functor C unit_univalent_double_cat}
           (τ θ : double_transformation F G)
  : τ = θ.
Proof.
  use double_transformation_eq.
  - intro.
    apply isasetunit.
  - intros x y f.
    apply isasetunit.
Qed.

(** * 5. The unit double category is a terminal object *)
Definition is_bifinal_unit_univalent_double_cat
  : is_bifinal unit_univalent_double_cat.
Proof.
  use make_is_bifinal.
  - exact (λ C, lax_double_functor_to_unit_double_cat C).
  - exact (λ C F G, double_transformation_to_unit_double_cat F G).
  - exact (λ C F G τ θ, double_transformation_to_unit_double_cat_eq τ θ).
Defined.
