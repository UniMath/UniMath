(*******************************************************************************************

 The full sub double category

 In this file, we define the full sub double category. To do so, we use the fact that the
 full subcategory can be defined via a displayed category.

 Contents
 1. The full sub double category
 2. Properties of this double category
 3. Univalence and strictness

 *******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.TwoSidedDispCatOnDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.
Require Import UniMath.Bicategories.DoubleCategories.Examples.DoubleCatOnDispCat.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. The full sub double category *)
Definition full_sub_double_cat
           (C : double_cat)
           (P : C → UU)
  : double_cat.
Proof.
  use double_cat_on_disp_cat.
  - exact C.
  - use disp_full_sub.
    exact P.
Defined.

(** * 2. Properties of this double category *)
Definition ver_weq_square_full_sub_double_cat
           (C : double_cat)
           (P : C → UU)
           (H : ver_weq_square C)
  : ver_weq_square (full_sub_double_cat C P).
Proof.
  use ver_weq_square_double_cat_on_disp_cat.
  - exact H.
  - apply disp_full_sub_locally_prop.
Defined.

Definition all_companions_full_sub_double_cat
           (C : double_cat)
           (P : C → UU)
           (H : all_companions_double_cat C)
  : all_companions_double_cat (full_sub_double_cat C P).
Proof.
  use all_companions_double_cat_on_disp_cat.
  exact H.
Defined.

Definition all_conjoints_full_sub_double_cat
           (C : double_cat)
           (P : C → UU)
           (H : all_conjoints_double_cat C)
  : all_conjoints_double_cat (full_sub_double_cat C P).
Proof.
  use all_conjoints_double_cat_on_disp_cat.
  exact H.
Defined.

(** * 3. Univalence and strictness *)
Definition univalent_full_sub_double_cat
           (C : univalent_double_cat)
           (P : C → hProp)
  : univalent_double_cat.
Proof.
  use univalent_double_cat_on_disp_cat.
  - exact C.
  - simple refine (_ ,, _).
    + exact (disp_full_sub C P).
    + abstract
        (use disp_full_sub_univalent ;
         intro ;
         apply propproperty).
Defined.

Definition full_sub_pseudo_double_set_cat
           (C : pseudo_double_setcat)
           (P : C → hProp)
  : pseudo_double_setcat.
Proof.
  use pseudo_double_set_cat_on_disp_cat.
  - exact C.
  - exact (disp_full_sub C P).
  - abstract
      (intro ;
       apply isasetaprop ;
       apply propproperty).
Defined.
