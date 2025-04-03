Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
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

Definition magma_cat
  : category
  := total_category magma_disp_cat.

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

Definition abelian_magma_disp_cat
  : disp_cat magma_cat
  := disp_full_sub magma_cat (λ X, iscomm (op (X := X))).

Definition semigroup_disp_cat
  : disp_cat magma_cat
  := disp_full_sub magma_cat (λ X, isassoc (op (X := X))).

Definition unital_magma_disp_cat
  : disp_cat magma_cat.
Proof.
  use disp_struct.
  - intro X.
    exact (isunital (op (X := X))).
  - refine (λ X Y uX uY (f : magma_morphism X Y), _).
    exact (f (pr1 uX) = pr1 uY).
  - abstract (
      intros;
      apply setproperty
    ).
  - abstract easy.
  - abstract (
      refine (λ X Y Z uX uY uZ (f g : magma_morphism _ _) Hf Hg, _);
      refine (_ @ Hg);
      apply (maponpaths g);
      apply Hf
    ).
Defined.

Definition monoid_disp_cat
  : disp_cat magma_cat
  := dirprod_disp_cat semigroup_disp_cat unital_magma_disp_cat.

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

Definition abelian_monoid_disp_cat
  : disp_cat magma_cat
  := dirprod_disp_cat monoid_disp_cat abelian_magma_disp_cat.

Definition abelian_group_disp_cat
  : disp_cat magma_cat
  := dirprod_disp_cat group_disp_cat abelian_magma_disp_cat.

Lemma is_univalent_abelian_group_disp_cat
  : is_univalent_disp abelian_group_disp_cat.
Proof.
  apply dirprod_disp_cat_is_univalent.
  - apply is_univalent_sigma_disp.
    + apply dirprod_disp_cat_is_univalent.
      * apply disp_full_sub_univalent.
        intro X.
        apply isapropisassoc.
      * apply is_univalent_disp_iff_fibers_are_univalent.
        refine (λ (X : magma) (u u' : isunital _), _).
        use isweq_iso.
        -- intro f.
          apply proofirrelevance.
          apply isapropisunital.
        -- intro x.
          apply proofirrelevance.
          apply isasetaprop.
          apply isapropisunital.
        -- intro x.
          apply z_iso_eq.
          apply setproperty.
    + apply is_univalent_disp_iff_fibers_are_univalent.
      intros X inv inv'.
      use isweq_iso.
      -- intro f.
        apply subtypePath.
        {
          intro.
          apply isapropisinv.
        }
        apply funextfun.
        intro x.
        exact (z_iso_mor f x).
      -- intro x.
        apply proofirrelevance.
        refine ((_ : isaset _) _ _).
        simple refine (isaset_carrier_subset (make_hSet _ _) (λ _, make_hProp _ _)).
        ++ apply funspace_isaset.
          apply setproperty.
        ++ apply isapropisinv.
      -- intro x.
        apply z_iso_eq.
        apply proofirrelevance.
        apply impred_isaprop.
        intro.
        apply setproperty.
  - apply disp_full_sub_univalent.
    intro X.
    apply isapropiscomm.
Defined.
