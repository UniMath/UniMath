Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Posets.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Definition poset_monoidal_cat
  : monoidal_cat.
Proof.
  refine (category_of_posets ,, _).
  use cartesianmonoidalcat.
  - exact BinProducts_category_of_posets.
  - exact Terminal_category_of_posets.
Defined.
