(********************************************************************

 The symmetric monoidal closed category of posets

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Definition poset_monoidal_cat
  : monoidal_cat.
Proof.
  refine (category_of_posets ,, _).
  use cartesian_monoidalcat.
  - exact BinProducts_category_of_posets.
  - exact Terminal_category_of_posets.
Defined.

Proposition is_cartesian_poset_monoidal_cat
  : is_cartesian poset_monoidal_cat.
Proof.
  apply is_cartesian_cartesian_monoidalcat.
Qed.

Definition poset_sym_monoidal_cat
  : sym_monoidal_cat
  := poset_monoidal_cat ,, symmetric_cartesian_monoidalcat _ _ _.

Definition poset_sym_mon_closed_cat
  : sym_mon_closed_cat.
Proof.
  use sym_mon_closed_cartesian_cat.
  - exact category_of_posets.
  - exact BinProducts_category_of_posets.
  - exact Terminal_category_of_posets.
  - exact Exponentials_category_of_posets.
Defined.
