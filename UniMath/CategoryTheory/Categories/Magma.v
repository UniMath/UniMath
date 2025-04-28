(**

  The Category of Magmas and Related Categories

  This file defines the category of magmas.
  It defines the categories of abelian magmas, semigroups and unital magmas as displayed categories
  over the category of magmas.
  It then defines the category of monoids as a displayed product category of semigroups and unital
  magmas.
  The category of groups is constructed via a displayed category over the category of monoids.
  Lastly, the categories of abelian groups and abelian monoids are again a displayed product of
  their respective category and the category of abelian magmas.
  For the categories that do not have their own files in this package (magmas, abelian magmas,
  semigroups and unital magmas), univalence is shown here.

  Contents
  1. The category of magmas [magma_category] [is_univalent_magma_category]
  1.1. Magmas [magma]
  1.2. Magma morphisms [magma_morphism]
  2. The category of abelian magmas [abelian_magma_disp_cat] [is_univalent_abelian_magma_disp_cat]
  3. The category of semigroups [semigroup_disp_cat] [is_univalent_semigroup_disp_cat]
  4. The category of unital magmas [unital_magma_disp_cat] [is_univalent_unital_magma_disp_cat]
  5. The category of monoids [monoid_category]
  6. The category of abelian monoids [abelian_monoid_category]
  7. The category of groups [group_category]
  8. The category of abelian groups [abelian_group_category]

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.CategoryWithStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Local Open Scope cat.

(** * 1. The category of magmas *)

Definition magma_disp_cat
  : disp_cat HSET.
Proof.
  use disp_struct.
  - refine (λ (X : hSet), binop X).
  - refine (λ X Y op op' f, ∏ x y, f (op x y) = op' (f x) (f y)).
  - abstract (
      intros;
      do 2 (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract easy.
  - abstract (
      intros X Y Z opX opY opZ f g Hf Hg x y;
      refine (_ @ Hg _ _);
      apply (maponpaths g);
      apply Hf
    ).
Defined.

Lemma is_univalent_magma_disp_cat
  : is_univalent_disp magma_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros X op op'.
  use isweq_iso.
  - intro f.
    apply funextfun.
    intro x.
    apply funextfun.
    intro y.
    exact (z_iso_mor f x y).
  - abstract (
      intro;
      apply proofirrelevance;
      apply isasetbinoponhSet
    ).
  - abstract (
      intro;
      apply z_iso_eq;
      apply proofirrelevance;
      do 2 (apply impred_isaprop; intro);
      apply setproperty
    ).
Defined.

Definition magma_category
  : category
  := total_category magma_disp_cat.

Lemma is_univalent_magma_category
  : is_univalent magma_category.
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_HSET.
  - apply is_univalent_magma_disp_cat.
Defined.

(** ** 1.1. Magmas *)

Definition magma
  : UU
  := magma_category.

Coercion magma_to_setwithbinop (X : magma) : setwithbinop := X.

(** ** 1.2. Magma morphisms *)

Definition magma_morphism
  (X Y : magma)
  : UU
  := magma_category⟦X, Y⟧.

Coercion magma_morphism_to_binopfun
  {X Y : magma}
  (f : magma_morphism X Y)
  : binopfun X Y
  := f.

(** * 2. The category of abelian magmas *)

Definition abelian_magma_disp_cat
  : disp_cat magma_category
  := disp_full_sub magma_category (λ X, iscomm (op (X := X))).

Lemma is_univalent_abelian_magma_disp_cat
  : is_univalent_disp abelian_magma_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  intro.
  apply isapropiscomm.
Defined.

(** * 3. The category of semigroups *)

Definition semigroup_disp_cat
  : disp_cat magma_category
  := disp_full_sub magma_category (λ X, isassoc (op (X := X))).

Lemma is_univalent_semigroup_disp_cat
  : is_univalent_disp semigroup_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  intro.
  apply isapropisassoc.
Defined.

(** * 4. The category of unital magmas *)

Definition unital_magma_disp_cat
  : disp_cat magma_category.
Proof.
  use disp_struct.
  - intro X.
    exact (isunital (op (X := X))).
  - refine (λ X Y uX uY (f : magma_morphism X Y), _).
    exact (f (pr1 uX) = pr1 uY).
  - abstract (intros; apply setproperty).
  - abstract easy.
  - abstract (
      refine (λ X Y Z uX uY uZ (f g : magma_morphism _ _) Hf Hg, _);
      refine (_ @ Hg);
      apply (maponpaths g);
      apply Hf
    ).
Defined.

Lemma is_univalent_unital_magma_disp_cat
  : is_univalent_disp unital_magma_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  refine (λ (X : magma) (u u' : isunital _), _).
  use isweq_iso.
  - intro f.
    apply proofirrelevance.
    apply isapropisunital.
  - abstract (intro; apply proofirrelevance, isasetaprop, isapropisunital).
  - abstract (intro; apply z_iso_eq, setproperty).
Defined.

(** * 5. The category of monoids *)

Definition monoid_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat semigroup_disp_cat unital_magma_disp_cat.

Definition monoid_category
  : category
  := total_category monoid_disp_cat.

(** * 6. The category of abelian monoids *)

Definition abelian_monoid_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat monoid_disp_cat abelian_magma_disp_cat.

Definition abelian_monoid_category
  : category
  := total_category abelian_monoid_disp_cat.

(** * 7. The category of groups *)

Definition group_disp_cat
  : disp_cat magma_category.
Proof.
  apply (sigma_disp_cat (D := monoid_disp_cat)).
  use disp_struct.
  - intro X.
    exact (invstruct op (pr2 X)).
  - intros X Y invX invY f.
    exact (∏ x, (pr1 f : magma_morphism _ _) (pr1 invX x) = pr1 invY ((pr1 f : magma_morphism _ _) x)).
  - abstract (
      intros;
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
  - abstract easy.
  - abstract (
      intros X Y Z opX opY opZ f g Hf Hg x;
      refine (_ @ Hg _);
      apply (maponpaths (pr1 g : magma_morphism _ _));
      apply Hf
    ).
Defined.

Definition group_category
  : category
  := total_category group_disp_cat.

(** * 8. The category of abelian groups *)

Definition abelian_group_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat group_disp_cat abelian_magma_disp_cat.

Definition abelian_group_category
  : category
  := total_category abelian_group_disp_cat.
