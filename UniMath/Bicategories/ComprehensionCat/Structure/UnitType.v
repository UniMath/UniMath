(*******************************************************************************************

 Comprehension categories with unit types

 In this file, we define the displayed bicategory of unit types for comprehension categories,
 and we show that this displayed bicategory is univalent. Since we are using univalent
 comprehension categories, we define this displayed bicategory as a subbicategory of the
 bicategory of comprehension categories.

 Contents
 1. The displayed bicategory of unit types
 2. The univalence of this displayed bicategory

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

(** * 1. The displayed bicategory of unit types *)
Definition disp_bicat_of_unit_type
  : disp_bicat bicat_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : comp_cat),
           fiberwise_terminal (cleaving_of_types C)).
  - exact (λ (C₁ C₂ : comp_cat)
             (T₁ : fiberwise_terminal (cleaving_of_types C₁))
             (T₂ : fiberwise_terminal (cleaving_of_types C₂))
             (F : comp_cat_functor C₁ C₂),
           ∏ (x : C₁),
           preserves_terminal
             (fiber_functor (comp_cat_type_functor F) x)).
  - abstract
      (intros C T x y Hy ;
       exact Hy).
  - abstract
      (intros C₁ C₂ C₃ T₁ T₂ T₃ F G HF HG x y Hy ;
       apply HG ;
       apply HF ;
       exact Hy).
Defined.

(** * 2. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_unit_type
  : disp_univalent_2_1 disp_bicat_of_unit_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ T₁ T₂ f.
  use impred ; intro.
  apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_0_disp_bicat_of_unit_type
  : disp_univalent_2_0 disp_bicat_of_unit_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_comp_cat.
  - intro C.
    apply isaprop_fiberwise_terminal.
  - intros C₁ C₂ T₁ T₂ f.
    use impred ; intro.
    apply isaprop_preserves_terminal.
Qed.

Definition univalent_2_disp_bicat_of_unit_type
  : disp_univalent_2 disp_bicat_of_unit_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_unit_type.
  - exact univalent_2_1_disp_bicat_of_unit_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_unit_type
  : disp_2cells_isaprop disp_bicat_of_unit_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_unit_type
  : disp_locally_groupoid disp_bicat_of_unit_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_comp_cat.
Qed.
