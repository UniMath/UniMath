(*******************************************************************************************

 The bicategory of categories with a cleaving and a terminal object

 Our goal is to construct the bicategory of full comprehension categories, and to do so, we
 use displayed bicategories. Starting with the bicategory of univalent categories, we add the
 following structure to it in the following order.
 1. A displayed category and a terminal object.
 2. A cleaving for the displayed category.
 3. A comprehension functor.
 4. A proof that this comprehension functor is fully faithful.
 In this file, we look at the second of these.

 To add the desired structure, we use a subbicategory. This subbicategory is defined as
 follows.
 1. The property that we require for the objects, is that the displayed category comes with
    a cleaving. Note that since we are working with univalent (displayed) categories,
    cleavings are unique, and for this reason, we have a proposition of cleavings.
 2. The property that we require for the displayed 1-cells, is that the displayed functor
    is cartesian. Being cartesian is always a proposition irregardless of whether we assume
    univalence or not.
 The univalence of this bicategory again follows from standard constructions. We only need to
 verify that cleavings are unique (which follows from univalence) and that being cartesian is
 a property.

 Contents
 1. The bicategory of categories with a terminal object and a fibration
 2. Builders and accessors

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.DispCatTerminal.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.

Local Open Scope cat.

(** * 1. The bicategory of categories with a terminal object and a fibration *)
Definition disp_bicat_cat_with_terminal_cleaving
  : disp_bicat bicat_cat_with_terminal_disp_cat.
Proof.
  use disp_subbicat.
  - exact (λ C, cleaving (disp_cat_of_types C)).
  - exact (λ C₁ C₂ D₁ D₂ F, is_cartesian_disp_functor (comp_cat_type_functor F)).
  - abstract
      (intros X fibX x y f xx yy ff p ;
       exact p).
  - abstract
      (intros X Y Z F G fibX fibY fibZ cartF cartG x y f xx yy ff p ; simpl ;
       apply cartG ;
       apply cartF ;
       exact p).
Defined.

Proposition disp_univalent_2_1_disp_bicat_cat_with_terminal_cleaving
  : disp_univalent_2_1 disp_bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_is_cartesian_disp_functor.
Qed.

Proposition disp_univalent_2_0_disp_bicat_cat_with_terminal_cleaving
  : disp_univalent_2_0 disp_bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_with_terminal_disp_cat.
  - intro.
    apply isaprop_cleaving.
    apply disp_univalent_category_is_univalent_disp.
  - intros.
    apply isaprop_is_cartesian_disp_functor.
Qed.

Definition bicat_cat_with_terminal_cleaving
  : bicat
  := total_bicat disp_bicat_cat_with_terminal_cleaving.

Proposition is_univalent_2_1_bicat_cat_with_terminal_cleaving
  : is_univalent_2_1 bicat_cat_with_terminal_cleaving.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_cat_with_terminal_disp_cat.
  - exact disp_univalent_2_1_disp_bicat_cat_with_terminal_cleaving.
Qed.

Proposition is_univalent_2_0_bicat_cat_with_terminal_cleaving
  : is_univalent_2_0 bicat_cat_with_terminal_cleaving.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_disp_cat.
  - exact disp_univalent_2_0_disp_bicat_cat_with_terminal_cleaving.
Qed.

Proposition is_univalent_2_bicat_cat_with_terminal_cleaving
  : is_univalent_2 bicat_cat_with_terminal_cleaving.
Proof.
  split.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
Qed.

(** * 2. Builders and accessors *)
Definition cat_with_terminal_cleaving
  : UU
  := bicat_cat_with_terminal_cleaving.

Definition make_cat_with_terminal_cleaving
           (C : cat_with_terminal_disp_cat)
           (DC : cleaving (disp_cat_of_types C))
  : cat_with_terminal_cleaving
  := C ,, DC ,, tt.

Coercion cat_terminal_disp_cat_of_cat_with_terminal_disp_cat
         (C : cat_with_terminal_cleaving)
  : cat_with_terminal_disp_cat
  := pr1 C.

Definition cleaving_of_types
           (C : cat_with_terminal_cleaving)
  : cleaving (disp_cat_of_types C)
  := pr12 C.

Definition functor_with_terminal_cleaving
           (C₁ C₂ : cat_with_terminal_cleaving)
  : UU
  := C₁ --> C₂.

Definition make_functor_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : functor_with_terminal_disp_cat C₁ C₂)
           (HF : is_cartesian_disp_functor (comp_cat_type_functor F))
  : functor_with_terminal_cleaving C₁ C₂
  := F ,, tt ,, HF.

Coercion functor_terminal_disp_cat_of_functor_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving}
         (F : functor_with_terminal_cleaving C₁ C₂)
  : functor_with_terminal_disp_cat C₁ C₂
  := pr1 F.

Definition is_cartesian_comp_cat_type_functor
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : functor_with_terminal_cleaving C₁ C₂)
  : is_cartesian_disp_functor (comp_cat_type_functor F)
  := pr22 F.

Definition nat_trans_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F G : functor_with_terminal_cleaving C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           {F G : functor_with_terminal_cleaving C₁ C₂}
           (τ : nat_trans_with_terminal_disp_cat F G)
  : nat_trans_with_terminal_cleaving F G
  := τ ,, tt ,, tt.

Coercion nat_trans_with_terminal_disp_cat_of_nat_trans_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving}
         {F G : functor_with_terminal_cleaving C₁ C₂}
         (τ : nat_trans_with_terminal_cleaving F G)
  : nat_trans_with_terminal_disp_cat F G
  := pr1 τ.
