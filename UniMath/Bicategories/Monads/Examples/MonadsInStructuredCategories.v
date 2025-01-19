Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
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
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInTotalBicat.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.

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
    + exact (TC ,, tt).
    + exact (tt ,, MT).
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
    + exact (BC ,, tt).
    + exact (tt ,, MB).
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
    + exact (PC ,, tt).
    + exact (tt ,, MP).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 4. Monads in the bicategory of categories with finite limits
 *)
Definition make_mnd_bicat_of_univ_cat_with_finlim
           (C : univalent_category)
           (M : Monad C)
           (TC : Terminal C)
           (PC : Pullbacks C)
           (MT : preserves_terminal M)
           (MP : preserves_pullback M)
  : mnd bicat_of_univ_cat_with_finlim.
Proof.
  use make_mnd_total_bicat.
  - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_subbicat.
  - use Monad_to_mnd_bicat_of_univ_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact ((TC ,, tt) ,, (PC ,, tt)).
    + exact ((tt ,, MT) ,, (tt ,, MP)).
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
    + exact (IC ,, tt).
    + exact (tt ,, MI).
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
    + exact (SC ,, tt).
    + exact (tt ,, MS).
    + exact (tt ,, tt).
    + exact (tt ,, tt).
Defined.

(**
 7. Monads in the bicategory of actegories
 *)
Definition make_mnd_actegory
           (V : category)
           (Mon_V : monoidal V)
           (C : category)
           (M : Monad C)
           (Act : actegory Mon_V C)
           (Ml : lineator_lax Mon_V Act Act M)
           (ηlinear : is_linear_nat_trans (identity_lineator_lax Mon_V Act) Ml (η M))
           (μlinear : is_linear_nat_trans (comp_lineator_lax Mon_V Ml Ml) Ml (μ M))
  : mnd (actbicat Mon_V).
Proof.
  use make_mnd_total_bicat.
  - apply actbicat_disp_2cells_isaprop.
  - use Monad_to_mnd_bicat_of_cats.
    + exact C.
    + exact M.
  - use make_disp_mnd.
    + exact Act.
    + exact Ml.
    + exact ηlinear.
    + exact μlinear.
Defined.
