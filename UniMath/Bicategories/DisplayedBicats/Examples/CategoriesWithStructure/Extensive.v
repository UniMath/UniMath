(*
  In this file, we define the bicategory of extensive categories and binary coproduct-preserving functors.

  Contents:
  - Definition of the bicategory of extensive categories [disp_bicat_extensive_cats]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodExtensivity.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.FiniteColimits.

Local Open Scope cat.

Section ExtensiveCategories.

  Definition disp_bicat_extensive_cats'
    : disp_bicat (total_bicat disp_bicat_bincoproducts).
  Proof.
    use disp_fullsubbicat.
    exact (λ C, is_extensive (pr12 C)).
  Defined.

  Definition disp_bicat_extensive_cats
    : disp_bicat bicat_of_cats
    := sigma_bicat _ _ disp_bicat_extensive_cats'.

  Lemma disp_2cells_iscontr_extensive_cats
    : disp_2cells_iscontr disp_bicat_extensive_cats.
  Proof.
    apply disp_2cells_of_sigma_iscontr.
    - apply disp_2cells_iscontr_bincoproducts.
    - apply disp_2cells_iscontr_fullsubbicat.
  Qed.

End ExtensiveCategories.
