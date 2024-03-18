(*******************************************************************************************

 Categories satisfying an additional property

 We define the bicategory of categories with finite limits satisfying an additional property.
 There are several interesting properties that we could instantiate this with, such as
 exactness, having a initial stable under pullback, having binary coproducts stable under
 pullback, extensiveness, having a subobject classifier, etcetera. We show that this
 bicategory is univalent and we show that every displayed morphism over an adjoint equivalence
 is again an adjoint equivalence.

 Contents
 1. The displayed bicategory arising from a categorical property
 2. The univalence of this bicategory
 3. Displayed adjoint equivalences in this bicategory

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.

Local Open Scope cat.

(** * 1. The displayed bicategory arising from a categorical property *)
Definition disp_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : disp_bicat bicat_of_univ_cat_with_finlim.
Proof.
  use disp_subbicat.
  - exact (λ (C : univ_cat_with_finlim), P C).
  - exact (λ (C₁ C₂ : univ_cat_with_finlim)
             (H₁ : P C₁)
             (H₂ : P C₂)
             (F : functor_finlim C₁ C₂),
           cat_property_functor P H₁ H₂ F).
  - intros C H.
    apply cat_property_id_functor.
  - intros C₁ C₂ C₃ P₁ P₂ P₃ F G HF HG.
    exact (cat_property_comp_functor P HF HG).
Defined.

Definition bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : bicat
  := total_bicat (disp_bicat_of_univ_cat_with_cat_property P).

(** * 2. The univalence of this bicategory *)
Definition disp_univalent_2_1_disp_bicat_univ_cat_with_cat_property
           (P : cat_property)
  : disp_univalent_2_1 (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_cat_property_functor.
Qed.

Definition disp_univalent_2_0_disp_bicat_univ_cat_with_cat_property
           (P : cat_property)
  : disp_univalent_2_0 (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - intro C.
    apply isaprop_cat_property_ob.
  - intros.
    apply isaprop_cat_property_functor.
Qed.

Definition disp_univalent_2_disp_bicat_univ_cat_with_cat_property
           (P : cat_property)
  : disp_univalent_2 (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  split.
  - exact (disp_univalent_2_0_disp_bicat_univ_cat_with_cat_property P).
  - exact (disp_univalent_2_1_disp_bicat_univ_cat_with_cat_property P).
Defined.

Definition is_univalent_2_1_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : is_univalent_2_1 (bicat_of_univ_cat_with_cat_property P).
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
  - exact (disp_univalent_2_1_disp_bicat_univ_cat_with_cat_property P).
Defined.

Definition is_univalent_2_0_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : is_univalent_2_0 (bicat_of_univ_cat_with_cat_property P).
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
  - exact (disp_univalent_2_0_disp_bicat_univ_cat_with_cat_property P).
Defined.

Definition is_univalent_2_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : is_univalent_2 (bicat_of_univ_cat_with_cat_property P).
Proof.
  split.
  - exact (is_univalent_2_0_bicat_of_univ_cat_with_cat_property P).
  - exact (is_univalent_2_1_bicat_of_univ_cat_with_cat_property P).
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : disp_2cells_isaprop (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : disp_locally_groupoid (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property
           (P : cat_property)
  : disp_2cells_iscontr (disp_bicat_of_univ_cat_with_cat_property P).
Proof.
  apply disp_2cells_iscontr_subbicat.
Qed.

(** * 3. Displayed adjoint equivalences in this bicategory *)
Definition disp_adjoint_equiv_disp_bicat_of_univ_cat_with_cat_property
           {P : cat_property}
           {C₁ C₂ : bicat_of_univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_univ_cat_with_cat_property P C₁}
           {T₂ : disp_bicat_of_univ_cat_with_cat_property P C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  use disp_left_adjoint_equivalence_subbicat.
  - clear C₁ C₂ F HF T₁ T₂ FF.
    intros C₁ C₂ H₁ H₂ F HF.
    apply (cat_property_adj_equiv
             P
             (_ ,, pr1 (left_adjoint_equivalence_total_disp_weq _ _ HF))).
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.
