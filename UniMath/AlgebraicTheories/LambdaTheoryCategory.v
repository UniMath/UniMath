(* Defines the univalent category of lambda theories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.

Local Open Scope cat.

(* The category of the data of lambda theories *)
Definition lambda_theory_data_disp_cat
  : disp_cat algebraic_theory_cat.
Proof.
  use disp_struct.
  - exact (λ (T : algebraic_theory),
      (∏ n, (T n : hSet) → (T (S n) : hSet)) ×
      (∏ n, (T (S n) : hSet) → (T n : hSet))).
  - exact (λ _ _ appabs appabs' (F : algebraic_theory_morphism _ _),
      (∏ n t, F _ ((pr1 appabs) n t) = (pr1 appabs') n (F _ t)) ×
      (∏ n t, F _ ((pr2 appabs) n t) = (pr2 appabs') n (F _ t))).
  - intros.
    apply isapropdirprod;
    do 2 (apply impred; intro);
    apply setproperty.
  - now intros.
  - intros ? ? ? ? ? ? ? ? Fdata F'data.
    use tpair;
      do 2 intro.
    + exact (maponpaths _ (pr1 Fdata _ _) @ (pr1 F'data _ _)).
    + exact (maponpaths _ (pr2 Fdata _ _) @ (pr2 F'data _ _)).
Defined.

Lemma is_univalent_disp_lambda_theory_data_disp_cat
  : is_univalent_disp lambda_theory_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  refine (λ (T : algebraic_theory) _ _, _).
  use isweq_iso.
  - intro f.
    use pathsdirprod;
      do 2 (apply funextsec; intro);
      apply f.
  - intro.
    refine (maponpaths (λ x, _ x _) _ @ maponpaths _ _ @ !(pathsdirprod_eta x));
    refine (pr1 ((_ : isaset _) _ _ _ _));
      do 2 (apply (impred 2); intro);
      apply setproperty.
  - intro.
    apply z_iso_eq.
    refine (pr1 ((_ : isaprop _) _ _)).
    apply isapropdirprod;
    do 2 (apply impred; intro);
    apply setproperty.
Qed.

Definition lambda_theory_data_cat
  : category
  := total_category lambda_theory_data_disp_cat.

Lemma is_univalent_lambda_theory_data_cat
  : is_univalent lambda_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_algebraic_theory_cat.
  - exact is_univalent_disp_lambda_theory_data_disp_cat.
Qed.

Section Test.
  Goal ob lambda_theory_data_cat = lambda_theory_data.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory_data), lambda_theory_data_cat⟦L, L'⟧ = lambda_theory_data_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.

(* The category of lambda theories without beta or eta *)
Definition lambda_theory_disp_cat
  : disp_cat lambda_theory_data_cat
  := disp_full_sub lambda_theory_data_cat is_lambda_theory.

Lemma is_univalent_disp_lambda_theory_disp_cat
  : is_univalent_disp lambda_theory_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact isaprop_is_lambda_theory.
Qed.

Definition lambda_theory_cat
  : category
  := total_category lambda_theory_disp_cat.

Lemma is_univalent_lambda_theory_cat
  : is_univalent lambda_theory_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_lambda_theory_data_cat.
  - exact is_univalent_disp_lambda_theory_disp_cat.
Qed.

Section Test.
  Goal ob lambda_theory_cat = lambda_theory.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory), lambda_theory_cat⟦L, L'⟧ = lambda_theory_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.
