(*******************************************************************************************

 DFL full comprehension categories with fiberwise structure

 In this file, we define the bicategory of DFL full comprehension category that support some
 fiberwise structure. Concretely, this means that every fiber in some DFL full comprehension
 category has the desired structure and that the structure is preserved by taking pullbacks.
 A concrete example would be given by the following categorical property:
 - A category satisfies the property if it has a terminal object
 - A functor preserves the property if it preserves terminal objects
 A DFL full comprehension category  satisfies this property fiberwise if every fiber has a
 terminal object and if taking pullbacks preserves terminal objects.

 Contents
 1. The displayed bicategory of DFL comprehension categories with fiberwise structure
 2. Properties of this displayed bicategory
 3. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.

Local Open Scope cat.

(** * 1. The displayed bicategory of DFL comprehension categories with fiberwise structure *)
Definition disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_bicat bicat_of_dfl_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : dfl_full_comp_cat),
           fiberwise_cat_property P C).
  - exact (λ (C₁ C₂ : dfl_full_comp_cat)
             (H₁ : fiberwise_cat_property P C₁)
             (H₂ : fiberwise_cat_property P C₂)
             (F : dfl_full_comp_cat_functor C₁ C₂),
           fiberwise_cat_property_functor F H₁ H₂).
  - abstract
      (intros C H x ;
       exact (cat_property_fiber_functor_id' P C x (H x))).
  - abstract
      (intros C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG x ;
       exact (cat_property_fiber_functor_comp P (HF x) (HG _))).
Defined.

(** * 2. Properties of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ H₁ H₂ F.
  use impred ; intro.
  apply isaprop_cat_property_functor.
Qed.

Definition univalent_2_0_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
  - intro C.
    apply isaprop_fiberwise_cat_property.
  - intros.
    use impred ; intro.
    apply isaprop_cat_property_functor.
Qed.

Definition univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  split.
  - exact (univalent_2_0_disp_bicat_of_cat_property_dfl_full_comp_cat P).
  - exact (univalent_2_1_disp_bicat_of_cat_property_dfl_full_comp_cat P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_cat_property_dfl_full_comp_cat P).
Proof.
  apply disp_2cells_iscontr_subbicat.
Qed.

(** * 3. Adjoint equivalences *)
Definition fiberwise_cat_property_functor_adjequiv
           {P : cat_property}
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           (H₁ : fiberwise_cat_property P C₁)
           (H₂ : fiberwise_cat_property P C₂)
  : fiberwise_cat_property_functor (pr1 F) H₁ H₂.
Proof.
  revert C₁ C₂ F P H₁ H₂.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C P H₁ H₂ ; cbn.
  intro Γ ; cbn.
  assert (H₁ Γ = H₂ Γ) as p .
  {
    apply isaprop_cat_property_ob.
  }
  refine (transportf
            (λ z, cat_property_functor _ _ z _)
            p
            _).
  apply cat_property_fiber_functor_id'.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat_help
           {P : cat_property}
           {C₁ C₂ : bicat_of_dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {H₁ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P H₁ H₂ FF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C P T₁ T₂ FF.
  use disp_left_adjoint_equivalence_subbicat.
  - intros.
    exact (fiberwise_cat_property_functor_adjequiv (f ,, Hf) Ha Hb).
  - apply is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat
           {P : cat_property}
           {C₁ C₂ : bicat_of_dfl_full_comp_cat}
           (F : C₁ --> C₂)
           (HF : left_adjoint_equivalence F)
           {H₁ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₁}
           {H₂ : disp_bicat_of_cat_property_dfl_full_comp_cat P C₂}
           (FF : H₁ -->[ F ] H₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  apply (disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat_help (F ,, HF)).
Qed.
