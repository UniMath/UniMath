(*
  In set-theoretical foundations, there is a difference between chosen limits and existing limits.
  In this file, we define bicategories of categories with either chosen or existing (finite) limits.

  For the remainder of this paragraph, we focus on terminal objects.
  We have a bicategory of categories with chosen limits;
  the 1-cells are functors that preserve the chosen terminal objects up to strict equality.
  We also have a bicategory of categories with limits; the 1-cells are functors that preserve limits (up to iso).
  If we were to look at univalent categories, then these two bicategories coincide.
  Terminal objects are unique up to equality in univalent categories, so if we know that a terminal object exists, then we can choose one.
  In addition, since equality corresponds to isomorphism, the two notion of preservation also correspond.
  If we do not require the category to be univalent, then the two aforementioned bicategories are actually different.

  In this file, we define these different bicategories.
  The interest for these bicategories come from how the Rezk completion interacts with these notions.

  Note that [disp_bicat_chosen_terminal_obj] is defined as a subbicategory of the bicategory of categories,
  even though terminal objects are in general only unique up to equality in univalent categories.
  We use this construction more as a shortcut to obtain the desired definition.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.BinProducts.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Pullbacks.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Equalizers.

Local Open Scope cat.

Section CategoriesWithChosenFiniteLimitsAndPreservationIsCreation.

  Definition disp_bicat_limits : disp_bicat bicat_of_cats
    := disp_dirprod_bicat
         disp_bicat_terminal
         (disp_dirprod_bicat
            disp_bicat_binproducts
            (disp_dirprod_bicat
               disp_bicat_pullbacks
               disp_bicat_equalizers)).

  Lemma disp_2cells_iscontr_limits : disp_2cells_iscontr disp_bicat_limits.
  Proof.
    repeat apply disp_2cells_of_dirprod_iscontr ; apply disp_2cells_iscontr_subbicat.
    (* - apply disp_2cells_iscontr_terminal.
    - apply disp_2cells_iscontr_binproducts.
    - apply disp_2cells_iscontr_pullbacks.
    - apply disp_2cells_iscontr_equalizers. *)
  Qed.

End CategoriesWithChosenFiniteLimitsAndPreservationIsCreation.

Section CategoriesWithChosenFiniteLimitsAndPreservationUpToEquality.

  Definition disp_bicat_chosen_limits
    : disp_bicat bicat_of_cats
    := disp_dirprod_bicat
         disp_bicat_chosen_terminal
         (disp_dirprod_bicat
            disp_bicat_chosen_binproducts
            (disp_dirprod_bicat
               disp_bicat_chosen_pullbacks
               disp_bicat_chosen_equalizers)).

  Lemma disp_2cells_iscontr_chosen_limits
    : disp_2cells_iscontr disp_bicat_chosen_limits.
  Proof.
    repeat apply disp_2cells_of_dirprod_iscontr ; apply disp_2cells_iscontr_subbicat.
    (* - apply disp_2cells_iscontr_chosen_terminal.
    - apply disp_2cells_iscontr_chosen_binproducts.
    - apply disp_2cells_iscontr_chosen_pullbacks.
    - apply disp_2cells_iscontr_chosen_equalizers. *)
  Qed.

End CategoriesWithChosenFiniteLimitsAndPreservationUpToEquality.

Section CategoriesWithExistingFiniteLimitsAndPreservationIsCreation.

  Definition disp_bicat_have_limits
    : disp_bicat bicat_of_cats
    := disp_dirprod_bicat
         disp_bicat_have_terminal
         (disp_dirprod_bicat
            disp_bicat_have_binproducts
            (disp_dirprod_bicat
               disp_bicat_have_pullbacks
               disp_bicat_have_equalizers)).

  Lemma disp_2cells_iscontr_have_limits
    : disp_2cells_iscontr disp_bicat_have_limits.
  Proof.
    repeat apply disp_2cells_of_dirprod_iscontr ; apply disp_2cells_iscontr_subbicat.
    (* - apply disp_2cells_iscontr_chosen_terminal.
    - apply disp_2cells_iscontr_chosen_binproducts.
    - apply disp_2cells_iscontr_chosen_pullbacks.
    - apply disp_2cells_iscontr_chosen_equalizers. *)
  Qed.

End CategoriesWithExistingFiniteLimitsAndPreservationIsCreation.
