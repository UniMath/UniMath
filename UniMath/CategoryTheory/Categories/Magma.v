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

Definition magma_cat
  : category
  := total_category magma_disp_cat.

Lemma is_univalent_magma_cat
  : is_univalent magma_cat.
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_HSET.
  - apply is_univalent_magma_disp_cat.
Defined.

Definition magma
  : UU
  := magma_cat.

Coercion magma_set (X : magma) : hSet := pr1 X.

Definition op {X : magma} : X → X → X := pr2 X.

Definition magma_morphism
  (X Y : magma)
  : UU
  := magma_cat⟦X, Y⟧.

Definition magma_morphism_function
  {X Y : magma}
  (f : magma_morphism X Y)
  : X → Y
  := pr1 f.

Coercion magma_morphism_function : magma_morphism >-> Funclass.

(* Abelian magmas *)

Definition abelian_magma_disp_cat
  : disp_cat magma_cat
  := disp_full_sub magma_cat (λ X, iscomm (op (X := X))).

Lemma is_univalent_abelian_magma_disp_cat
  : is_univalent_disp abelian_magma_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  intro.
  apply isapropiscomm.
Defined.

(* Semigroups *)

Definition semigroup_disp_cat
  : disp_cat magma_cat
  := disp_full_sub magma_cat (λ X, isassoc (op (X := X))).

Lemma is_univalent_semigroup_disp_cat
  : is_univalent_disp semigroup_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  intro.
  apply isapropisassoc.
Defined.

(* Unital Magmas *)

Definition unital_magma_disp_cat
  : disp_cat magma_cat.
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
  : disp_cat magma_cat
  := dirprod_disp_cat semigroup_disp_cat unital_magma_disp_cat.

Definition is_univalent_monoid_disp_cat
  : is_univalent_disp monoid_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_semigroup_disp_cat
    is_univalent_unital_magma_disp_cat.

Definition monoid_cat
  : category
  := total_category monoid_disp_cat.

Definition is_univalent_monoid_cat
  : is_univalent monoid_cat
  := is_univalent_total_category
    is_univalent_magma_cat
    is_univalent_monoid_disp_cat.

(* Abelian Monoids *)

Definition abelian_monoid_disp_cat
  : disp_cat magma_cat
  := dirprod_disp_cat monoid_disp_cat abelian_magma_disp_cat.

Definition is_univalent_abelian_monoid_disp_cat
  : is_univalent_disp abelian_monoid_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_monoid_disp_cat
    is_univalent_abelian_magma_disp_cat.

Definition abelian_monoid_cat
  : category
  := total_category abelian_monoid_disp_cat.

Definition is_univalent_abelian_monoid_cat
  : is_univalent abelian_monoid_cat
  := is_univalent_total_category
    is_univalent_magma_cat
    is_univalent_abelian_monoid_disp_cat.

(* Groups *)

Definition group_disp_cat
  : disp_cat magma_cat.
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

Definition group_cat
  : category
  := total_category group_disp_cat.

Definition is_univalent_group_cat
  : is_univalent group_cat
  := is_univalent_total_category
    is_univalent_magma_cat
    is_univalent_group_disp_cat.

(* Abelian Groups *)

Definition abelian_group_disp_cat
  : disp_cat magma_cat
  := dirprod_disp_cat group_disp_cat abelian_magma_disp_cat.

Definition is_univalent_abelian_group_disp_cat
  : is_univalent_disp abelian_group_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_group_disp_cat
    is_univalent_abelian_magma_disp_cat.

Definition abelian_group_cat
  : category
  := total_category abelian_group_disp_cat.

Definition is_univalent_abelian_group_cat
  : is_univalent abelian_group_cat
  := is_univalent_total_category
    is_univalent_magma_cat
    is_univalent_abelian_group_disp_cat.

Require Import Algebra.Groups.
Require Import Algebra.Monoids.

Check (idpath _ : (monoid_cat : UU) = monoid).
Check (idpath _ : (abelian_monoid_cat : UU) = abmonoid).
Check (idpath _ : (group_cat : UU) = gr).
Check (idpath _ : (abelian_group_cat : UU) = abgr).
