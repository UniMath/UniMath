(**

  The Univalent Category of Groups

  This file shows that the category of groups, already defined in Magma.v, is univalent.

  Contents
  1. The univalent category of groups [group_univalent_category]

 *)
Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The univalent category of groups *)

Lemma is_univalent_group_disp_cat
  : is_univalent_disp group_disp_cat.
Proof.
  apply is_univalent_sigma_disp.
  - apply is_univalent_monoid_disp_cat.
  - apply is_univalent_disp_iff_fibers_are_univalent.
    intros X inv inv'.
    use isweq_iso.
    + intro f.
      apply (subtypePath (isapropisinv _ _)).
      apply funextfun.
      intro x.
      exact (z_iso_mor f x).
    + abstract (
        intro;
        apply proofirrelevance;
        simple refine (isaset_carrier_subset (make_hSet _ _) (λ _, make_hProp _ _) _ _);
        [ apply funspace_isaset;
          apply setproperty
        | apply isapropisinv ]
      ).
    + abstract (
        intro;
        apply z_iso_eq;
        apply proofirrelevance;
        apply impred_isaprop;
        intro;
        apply setproperty
      ).
Defined.

Definition is_univalent_group_category
  : is_univalent group_category
  := is_univalent_total_category
    is_univalent_magma_category
    is_univalent_group_disp_cat.

Definition group_univalent_category : univalent_category
  := make_univalent_category group_category is_univalent_group_category.
