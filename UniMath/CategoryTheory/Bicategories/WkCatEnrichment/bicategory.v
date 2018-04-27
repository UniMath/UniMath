Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.prebicategory.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.internal_equivalence.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.Notations.

(******************************************************************************)
(* Definition of bicategory *)

Definition is_bicategory (C : prebicategory) : UU
  := (has_homcats C) × (∏ (a b : C), isweq (path_to_adj_int_equivalence a b)).

Definition bicategory : UU := ∑ C : prebicategory, is_bicategory C.

(******************************************************************************)
(* Being a bicategory is a prop *)

Definition isaprop_has_homcats { C : prebicategory }
  : isaprop (has_homcats C).
Proof.
  apply impred.
  intro a.
  apply impred.
  intro b.
  apply (isaprop_is_univalent (a -1-> b)).
Qed.
