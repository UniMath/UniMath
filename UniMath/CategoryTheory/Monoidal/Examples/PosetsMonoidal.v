(********************************************************************

 Symmetric monoidal closed categories of posets

 We define two symmetric monoidal closed categories. One is the
 category of posets where the monoidal product is the cartesian
 product of posets. The other one is the category of pointed posets
 where the monoidal product is the smash product.

 Contents
 1. The cartesian monoidal category of posets
 2. The symmetric monoidal category of pointed posets

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.PointedPosetStrict.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SmashProductMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

(**
 1. The cartesian monoidal category of posets
 *)
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

(**
 2. The symmetric monoidal category of pointed posets
 *)
Definition pointed_poset_sym_mon_closed_cat
  : sym_mon_closed_cat.
Proof.
  use smash_product_sym_mon_closed_cat.
  exact pointed_struct_pointed_poset_strict_with_smash_closed.
Defined.
