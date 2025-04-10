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

(* Magmas *)

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

Definition magma
  : UU
  := magma_category.

Coercion magma_to_setwithbinop (X : magma) : setwithbinop := X.

Definition magma_morphism
  (X Y : magma)
  : UU
  := magma_category⟦X, Y⟧.

Definition magma_morphism_function
  {X Y : magma}
  (f : magma_morphism X Y)
  : X → Y
  := pr1 f.

Coercion magma_morphism_function : magma_morphism >-> Funclass.

(* Abelian magmas *)

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

(* Semigroups *)

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

(* Unital Magmas *)

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

(* Monoids *)

Definition monoid_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat semigroup_disp_cat unital_magma_disp_cat.

Definition monoid_category
  : category
  := total_category monoid_disp_cat.

(* Abelian Monoids *)

Definition abelian_monoid_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat monoid_disp_cat abelian_magma_disp_cat.

Definition abelian_monoid_category
  : category
  := total_category abelian_monoid_disp_cat.

(* Groups *)

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

(* Abelian Groups *)

Definition abelian_group_disp_cat
  : disp_cat magma_category
  := dirprod_disp_cat group_disp_cat abelian_magma_disp_cat.

Definition abelian_group_category
  : category
  := total_category abelian_group_disp_cat.
