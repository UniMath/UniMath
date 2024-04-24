(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

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

Definition top_cat
  : category
  := total_category disp_top.

Lemma is_univalent_top_cat
  : is_univalent top_cat.
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_HSET.
  - apply is_univalent_disp_iff_fibers_are_univalent.
    intros X Xdata Xdata'.
    use isweq_iso.
    + intro f.
      apply (subtypePath (λ _, isaprop_isSetOfOpen _)).
      apply funextfun.
      intro U.
      apply hPropUnivalence.
      * intro H.
        exact (pr1 (continuous_iff_reflects_open _) (pr1 (pr2 f)) (make_carrier _ _ H)).
      * intro H.
        exact (pr1 (continuous_iff_reflects_open _) (pr1 f) (make_carrier _ _ H)).
    + intro H.
      apply uip.
      apply isaset_total2.
      * apply isasethsubtype.
      * intro.
        apply isasetaprop.
        apply isaprop_isSetOfOpen.
    + intro H.
      apply (subtypePath (λ _, isaprop_is_z_isomorphism _)).
      apply isaprop_continuous.
Qed.
