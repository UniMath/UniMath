From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Algebra.DivisionRig.
Require Import UniMath.Algebra.ConstructiveStructures.

Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

(** * Displayed category of topological spaces

The displayed category of topological spaces, also known as the category of topological spaces with continuous maps, can be defined using a single line of code:
```coq
val top_disp_cat_ob_mor = make_disp_cat_ob_mor.
```
This definition uses the `make_disp_cat_ob_mor` function from the `hset_category` module to create a new category that satisfies the properties of being topological and having continuous maps between spaces. The `exact` statement is used to prove that this category matches the desired properties.

 *)

Definition top_disp_cat_ob_mor : disp_cat_ob_mor hset_category.
Proof.
  use make_disp_cat_ob_mor.
  - intro X. exact (isTopologicalSpace X).
  - intros X Y T U f.
    exact (@continuous (X,,T) (Y,,U) f).
Defined.


Definition top_disp_cat_data : disp_cat_data hset_category.
Proof.
  exists top_disp_cat_ob_mor.
  split.
  - do 5 intro. assumption.
  - intros *. apply continuous_funcomp.
Defined.

Definition top_disp_cat_axioms : disp_cat_axioms hset_category top_disp_cat_data.
Proof.
  do 3 (split ; intros ; try (apply proofirrelevance, isaprop_continuous)).
  apply isasetaprop, isaprop_continuous.
Defined.

Definition disp_top : disp_cat hset_category := _ ,, top_disp_cat_axioms.
