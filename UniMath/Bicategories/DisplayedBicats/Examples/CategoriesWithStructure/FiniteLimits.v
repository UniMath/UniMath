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
    repeat apply disp_2cells_of_dirprod_iscontr.
    - apply disp_2cells_iscontr_terminal.
    - apply disp_2cells_iscontr_binproducts.
    - apply disp_2cells_iscontr_pullbacks.
    - apply disp_2cells_iscontr_equalizers.
  Qed.

End CategoriesWithChosenFiniteLimitsAndPreservationIsCreation.
