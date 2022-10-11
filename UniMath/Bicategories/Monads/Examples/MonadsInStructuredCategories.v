Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfUnivCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInTotalBicat.

(**
 1. Monads in the bicategory of categories with a terminal object
 *)
Definition make_mnd_univ_cat_with_terminal_obj
           (C : univalent_category)
           (M : Monad C)
           (TC : Terminal C)
           (MT : preserves_terminal M)
  : mnd univ_cat_with_terminal_obj.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact (tt ,, TC).
    + exact (MT ,, tt).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 2. Monads in the bicategory of categories with binary products
 *)
Definition make_mnd_univ_cat_with_binprod
           (C : univalent_category)
           (M : Monad C)
           (BC : BinProducts C)
           (MB : preserves_binproduct M)
  : mnd univ_cat_with_binprod.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact (tt ,, BC).
    + exact (MB ,, tt).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 3. Monads in the bicategory of categories with pullbacks
 *)
Definition make_mnd_univ_cat_with_pb
           (C : univalent_category)
           (M : Monad C)
           (PC : Pullbacks C)
           (MP : preserves_pullback M)
  : mnd univ_cat_with_pb.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact (tt ,, PC).
    + exact (MP ,, tt).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 4. Monads in the bicategory of categories with finite limits
 *)
Definition make_mnd_univ_cat_with_finlim
           (C : univalent_category)
           (M : Monad C)
           (TC : Terminal C)
           (PC : Pullbacks C)
           (MT : preserves_terminal M)
           (MP : preserves_pullback M)
  : mnd univ_cat_with_finlim.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact ((tt ,, TC) ,, (tt ,, PC)).
    + exact ((MT ,, tt) ,, (MP ,, tt)).
    + cbn.
      exact ((tt ,, tt) ,, (tt ,, tt)).
    + cbn.
      exact ((tt ,, tt) ,, (tt ,, tt)).
Defined.

(**
 5. Monads in the bicategory of categories with an initial object
 *)
Definition make_mnd_univ_cat_with_initial
           (C : univalent_category)
           (M : Monad C)
           (IC : Initial C)
           (MI : preserves_initial M)
  : mnd univ_cat_with_initial.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact (tt ,, IC).
    + exact (MI ,, tt).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 6. Monads in the bicategory of categories with binary coproducts
 *)
Definition make_mnd_univ_cat_with_bincoprod
           (C : univalent_category)
           (M : Monad C)
           (SC : BinCoproducts C)
           (MS : preserves_bincoproduct M)
  : mnd univ_cat_with_bincoprod.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact (tt ,, SC).
    + exact (MS ,, tt).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.
