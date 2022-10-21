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

(** * Displayed category of topological spaces *)

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
