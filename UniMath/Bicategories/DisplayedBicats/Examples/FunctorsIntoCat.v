(******************************************************************************************

 The displayed bicategory of functors into categories

 In this file, we look at the displayed bicategory of functors into the category of strict categories. 
 Note that here, we restrict ourselves to functors starting in strict categories. 
 In addition, note that a functor into the category of strict categories is the same as a split opfibration on the source.

 Contents:
 1. Definition
 2. Properties

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.StrictCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.

Local Open Scope cat.

(**
 1. Definition
 *)
Definition disp_cat_ob_mor_of_functors_into_cat
  : disp_cat_ob_mor bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact (λ C, pr1 C ⟶ cat_of_setcategory).
  - exact (λ C₁ C₂ G₁ G₂ F, G₁ ⟹ F ∙ G₂).
Defined.

Definition disp_cat_id_comp_of_functors_into_cat
  : disp_cat_id_comp
      bicat_of_strict_cats
      disp_cat_ob_mor_of_functors_into_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ C G, nat_trans_id _).
  - exact (λ C₁ C₂ C₃ F₁ F₂ G₁ G₂ G₃ α β,
           nat_trans_comp
             _ _ _
             α
             (pre_whisker _ β)).
Defined.

Definition disp_cat_data_of_functors_into_cat
  : disp_cat_data bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_functors_into_cat.
  - exact disp_cat_id_comp_of_functors_into_cat.
Defined.

Definition disp_prebicat_1_id_comp_cells_of_functors_into_cat
  : disp_prebicat_1_id_comp_cells bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_functors_into_cat.
  - intros C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂.
    exact (∏ (x : pr1 C₁), pr1 β₁ x · # (pr1 G₂) (pr1 α x) = pr1 β₂ x).
Defined.

Definition disp_prebicat_ops_of_functors_into_cat
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_of_functors_into_cat.
Proof.
  repeat split.
  - intros C₁ C₂ F G₁ G₂ α x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₂).
    }
    exact (id_right (pr1 α x)).
  - intros C₁ C₂ F G₁ G₂ α x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₂).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (id_left (pr1 α x)).
    }
    exact (id_right (pr1 α x)).
  - intros C₁ C₂ F G₁ G₂ α x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₂).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (id_right (pr1 α x)).
    }
    exact (id_right (pr1 α x)).
  - intros C₁ C₂ F G₁ G₂ α x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₂).
    }
    exact (id_right (pr1 α x) @ !(id_left (pr1 α x))).
  - intros C₁ C'_2 F G₁ G₂ α x ; cbn.
    apply maponpaths.
    apply (functor_id G₂).
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ G₁ G₂ G₃ G₄ α₁ α₂ α₃ x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₄).
    }
    etrans.
    {
      exact (id_right (pr1 α₁ _ · pr1 α₂ _ · pr1 α₃ _)).
    }
    rewrite !assoc'.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ G₁ G₂ G₃ G₄ α₁ α₂ α₃ x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_id G₄).
    }
    etrans.
    {
      exact (id_right (pr1 α₁ _ · (pr1 α₂ _ · pr1 α₃ _))).
    }
    rewrite !assoc.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ α β G₁ G₂ γ₁ γ₂ γ₃ p₁ p₂ x ; cbn.
    etrans.
    {
      apply maponpaths.
      apply (functor_comp G₂).
    }
    refine (_ @ p₂ x).
    refine (_ @ maponpaths (λ z, z ∙ _) (p₁ x)).
    apply (assoc _ (# (pr1 G₂) (pr1 α x)) (# (pr1 G₂) (pr1 β x))).
  - intros C₁ C₂ C₃ F₁ F₂ F₃ α G₁ G₂ G₃ β₁ β₂ β₃ p x ; cbn.
    refine (assoc' (pr1 β₁ x) _ _ @ _).
    apply maponpaths.
    apply p.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ α G₁ G₂ G₃ β₁ β₂ β₃ p x ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(p _)).
    }
    refine (assoc' _ _ _ @ _ @ assoc (pr1 β₁ x) (pr1 β₃ (pr1 F₁ x)) _).
    apply maponpaths.
    apply (nat_trans_ax β₃).
Qed.

Definition disp_prebicat_data_of_functors_into_cat
  : disp_prebicat_data bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_of_functors_into_cat.
  - exact disp_prebicat_ops_of_functors_into_cat.
Defined.

Definition isaprop_2cells_of_functors_into_cat
           {C₁ C₂ : bicat_of_strict_cats}
           {F₁ F₂ : C₁ --> C₂}
           (α : F₁ ==> F₂)
           {G₁ : disp_prebicat_data_of_functors_into_cat C₁}
           {G₂ : disp_prebicat_data_of_functors_into_cat C₂}
           (β₁ : G₁ -->[ F₁ ] G₂)
           (β₂ : G₁ -->[ F₂ ] G₂)
  : isaprop (β₁ ==>[ α ] β₂).
Proof.
  use impred ; intro.
  apply homset_property.
Qed.

Definition disp_prebicat_laws_of_functors_into_cat
  : disp_prebicat_laws disp_prebicat_data_of_functors_into_cat.
Proof.
  repeat split ; intro ; intros ; apply isaprop_2cells_of_functors_into_cat.
Qed.

Definition disp_prebicat_of_functors_into_cat
  : disp_prebicat bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_of_functors_into_cat.
  - exact disp_prebicat_laws_of_functors_into_cat.
Defined.

Definition disp_bicat_of_functors_into_cat
  : disp_bicat bicat_of_strict_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_of_functors_into_cat.
  - intros C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂.
    apply isasetaprop.
    apply isaprop_2cells_of_functors_into_cat.
Defined.

(**
 2. Properties
 *)
Definition functors_into_cat_disp_2cells_isaprop
  : disp_2cells_isaprop disp_bicat_of_functors_into_cat.
Proof.
  intro ; intros.
  apply isaprop_2cells_of_functors_into_cat.
Qed.

Definition functors_into_cat_disp_locally_sym
  : disp_locally_sym disp_bicat_of_functors_into_cat.
Proof.
  intros C₁ C₂ F₁ F₂ α G₁ G₂ β₁ β₂ p x.
  etrans.
  {
    apply maponpaths_2.
    exact (!(p x)).
  }
  refine (assoc' (pr1 β₁ x) _ _ @ _ @ id_right _).
  apply maponpaths.
  refine (!(functor_comp G₂ _ _) @ _ @ functor_id G₂ _).
  apply maponpaths.
  exact (nat_trans_eq_pointwise (vcomp_rinv α) x).
Qed.

Definition functors_into_cat_disp_locally_groupoid
  : disp_locally_groupoid disp_bicat_of_functors_into_cat.
Proof.
  use make_disp_locally_groupoid.
  - exact functors_into_cat_disp_locally_sym.
  - exact functors_into_cat_disp_2cells_isaprop.
Defined.
