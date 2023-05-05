(********************************************************************

 The symmetric monoidal closed category of structured sets

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Definition monoidal_cat_of_hset_struct
           (P : hset_cartesian_struct)
  : monoidal_cat.
Proof.
  refine (category_of_hset_struct P ,, _).
  use cartesian_monoidal.
  - exact (BinProducts_category_of_hset_struct P).
  - exact (Terminal_category_of_hset_struct P).
Defined.

Proposition is_cartesian_cat_of_hset_struct
            (P : hset_cartesian_struct)
  : is_cartesian (monoidal_cat_of_hset_struct P).
Proof.
  apply is_cartesian_cartesian_monoidalcat.
Qed.

Definition sym_monoidal_cat_of_hset_struct
           (P : hset_cartesian_struct)
  : sym_monoidal_cat
  := monoidal_cat_of_hset_struct P  ,, symmetric_cartesian_monoidalcat _ _ _.

Definition sym_mon_closed_cat_of_hset_struct
           (P : hset_cartesian_closed_struct)
  : sym_mon_closed_cat.
Proof.
  use sym_mon_closed_cartesian_cat.
  - exact (category_of_hset_struct P).
  - exact (BinProducts_category_of_hset_struct P).
  - exact (Terminal_category_of_hset_struct P).
  - exact (Exponentials_struct P).
Defined.
