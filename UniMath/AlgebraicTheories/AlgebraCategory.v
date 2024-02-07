(**************************************************************************************************

  Properties of the category of algebraic theory algebras

  The displayed category structure is leveraged to show that the category univalent. Also, a
  characterization of isomorphisms is given.

  Contents
  1. Univalence [is_univalent_algebra_cat]
  2. A characterization of iso's of algebras [make_algebra_z_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.

Local Open Scope cat.

(** * 1. Univalence *)

Lemma is_univalent_disp_algebra_data_full_disp_cat
  : is_univalent_disp algebra_data_full_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro f.
    do 3 (apply funextsec; intro).
    apply (z_iso_mor f _).
  - intro.
    do 3 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 3 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Lemma is_univalent_algebra_data_full_cat
  : is_univalent algebra_data_full_cat.
Proof.
  use is_univalent_total_category.
  - exact (is_univalent_cartesian' _ _ is_univalent_algebraic_theory_cat is_univalent_HSET).
  - exact is_univalent_disp_algebra_data_full_disp_cat.
Qed.

Lemma is_univalent_disp_algebra_full_disp_cat
  : is_univalent_disp algebra_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_full_is_algebra _).
Qed.

Lemma is_univalent_algebra_full_cat
  : is_univalent algebra_full_cat.
Proof.
  apply (is_univalent_total_category is_univalent_algebra_data_full_cat).
  exact is_univalent_disp_algebra_full_disp_cat.
Qed.

Lemma is_univalent_algebra_cat (T : algebraic_theory)
  : is_univalent (algebra_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  unfold algebra_disp_cat.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_disp_cartesian'.
    apply is_univalent_HSET.
  - exact is_univalent_disp_algebra_data_full_disp_cat.
  - exact is_univalent_disp_algebra_full_disp_cat.
Qed.

(** * 2. A characterization of iso's of algebras *)

Section Iso.

  Context (T : algebraic_theory).
  Context (A A' : algebra T).
  Context (F : z_iso (C := HSET) (A : hSet) (A' : hSet)).
  Context (Haction : ∏ n f a, mor_action_ax (identity T) (z_iso_mor F) (@action T A) (@action T A') n f a).

  Definition make_algebra_z_iso_mor
    : algebra_morphism A A'
    := make_algebra_morphism _ Haction.

  Definition make_algebra_z_iso_inv_data
    : A' → A
    := inv_from_z_iso F.

  Lemma make_algebra_z_iso_inv_action_ax
    : ∏ n f a, mor_action_ax (identity T) make_algebra_z_iso_inv_data (@action T A') (@action T A) n f a.
  Proof.
    intros n f a.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso F)).
    apply (maponpaths (inv_from_z_iso F)).
    refine (Haction _ _ _ @ _).
    apply maponpaths.
    apply funextfun.
    intro i.
    apply (eqtohomot (z_iso_after_z_iso_inv F)).
  Qed.

  Definition make_algebra_z_iso_inv
    : algebra_morphism A' A
    := make_algebra_morphism _ make_algebra_z_iso_inv_action_ax.

  Lemma make_algebra_z_iso_is_iso
    : is_inverse_in_precat (C := algebra_cat T)
      make_algebra_z_iso_mor
      make_algebra_z_iso_inv.
  Proof.
    split;
      apply algebra_morphism_eq;
      refine (algebra_mor_comp _ _ @ _).
    - apply (z_iso_inv_after_z_iso F).
    - apply (z_iso_after_z_iso_inv F).
  Qed.

  Definition make_algebra_z_iso
    : z_iso (C := algebra_cat T) A A'
    := make_z_iso (C := algebra_cat T)
      make_algebra_z_iso_mor
      make_algebra_z_iso_inv
      make_algebra_z_iso_is_iso.

End Iso.
