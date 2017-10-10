(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Algebra.DivisionRig.
Require Import UniMath.Algebra.ConstructiveStructures.

Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

(** * Displayed category of topological spaces *)


Definition top_disp_cat_ob_mor : disp_cat_ob_mor HSET.
Proof.
  mkpair.
  - intro X. exact (isTopologicalSet (pr1hSet X)).
  - cbn. intros X Y T U f.
    apply (@continuous (pr1hSet X,,T) (pr1hSet Y,,U) f).
Defined.

Definition top_disp_cat_data : disp_cat_data HSET.
Proof.
  exists top_disp_cat_ob_mor.
  mkpair.
  - intros X XX. cbn. unfold continuous. intros.
    unfold continuous_at. cbn. unfold is_lim. cbn.
    unfold filterlim. cbn. unfold filter_le. cbn.
    intros. assumption.
  - intros X Y Z f g XX YY ZZ Hf Hg.
    use (@continuous_funcomp (pr1hSet X,,XX) (pr1hSet Y,,YY) (pr1hSet Z,,ZZ) f g);
      assumption.
Defined.

Definition top_disp_cat_axioms : disp_cat_axioms SET top_disp_cat_data.
Proof.
  repeat split; cbn; intros; try (apply proofirrelevance, isaprop_continuous).
  apply isasetaprop. apply isaprop_continuous.
Defined.

Definition disp_top : disp_cat SET := _ ,, top_disp_cat_axioms.
