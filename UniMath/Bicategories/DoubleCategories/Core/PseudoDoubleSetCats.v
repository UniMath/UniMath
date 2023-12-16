(**********************************************************************************


 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfTwoSidedDispCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.CatOfPseudoDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.

Local Open Scope cat.

(** * 1. Univalent double categories *)
Definition pseudo_double_setcat
  : UU
  := ob univalent_cat_of_pseudo_double_setcategory.

(** * 2. Accessors for univalent double categories *)
Coercion pseudo_double_setcat_to_double_cat
         (C : pseudo_double_setcat)
  : double_cat
  := make_double_cat
       _
       _
       _
       _
       _
       _
       _
       (pr12 C)
       (pr22 C).

Proposition is_setcategory_vertical_cat
            (C : pseudo_double_setcat)
  : is_setcategory C.
Proof.
  exact (pr21 (pr111 C)).
Qed.

Proposition is_strict_twosided_disp_cat_hor_mor
            (C : pseudo_double_setcat)
  : is_strict_twosided_disp_cat (hor_mor C).
Proof.
  exact (pr22 (pr111 C)).
Qed.

(** * 3. Builder for double categories *)
Definition make_pseudo_double_setcat
           (C : double_cat)
           (HC : is_setcategory C)
           (HD : is_strict_twosided_disp_cat (hor_mor C))
  : pseudo_double_setcat.
Proof.
  simple refine ((((_ ,, _) ,, _) ,, _) ,, _).
  - exact (_ ,, HC).
  - exact (_ ,, HD).
  - exact (hor_id_double_cat C ,, hor_comp_double_cat C).
  - exact (double_cat_double_lunitor C
           ,,
           double_cat_double_runitor C
           ,,
           double_cat_double_associator C).
  - exact (@double_triangle C ,, @double_pentagon C).
Defined.
