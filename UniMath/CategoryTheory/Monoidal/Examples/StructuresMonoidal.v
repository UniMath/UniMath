Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.StructureWithProd.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Definition monoidal_cat_of_hset_struct
           (P : hset_struct)
  : monoidal_cat.
Proof.
  refine (category_of_hset_struct P ,, _).
  use cartesianmonoidalcat.
  - exact (BinProducts_category_of_hset_struct P).
  - exact (Terminal_category_of_hset_struct P).
Defined.
