(* Defines the univalent category of algebraic theories. *)

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Require Import UniMath.AlgebraicTheories.Tactics.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition base_functor_category
  : category
  := [finite_set_skeleton_category, HSET].

Definition pointed_functor_disp_cat
  : disp_cat base_functor_category.
Proof.
  use disp_struct.
  - intro T.
    exact ((T : base_functor) 1 : hSet).
  - intros T T' Tdata T'data F.
    exact ((F : base_nat_trans _ _) _ Tdata = T'data).
  - abstract (intros; prove_hlevel).
  - now intros.
  - intros T T' T'' e e' e'' F F' HF HF'.
    now rewrite (!HF'), (!HF).
Defined.

Definition pointed_functor_cat
  : category
  := total_category pointed_functor_disp_cat.

Definition algebraic_theory_data_disp_cat
  : disp_cat pointed_functor_cat.
Proof.
  use disp_struct.
  - exact (λ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)).
  - exact (λ T T' Tdata T'data (F : pointed_functor_morphism T T'),
      ∏ m n f g, (F _ (Tdata m n f g)) = T'data m n (F _ f) (λ i, F _ (g i))).
  - intros.
    prove_hlevel.
  - now intros.
  - intros T T' T'' Tdata T'data T''data F F' Fdata F'data m n f g.
    cbn.
    now rewrite Fdata, F'data.
Defined.

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat
  := disp_full_sub algebraic_theory_data_cat is_algebraic_theory.

Definition algebraic_theory_cat
  : category
  := total_category algebraic_theory_disp_cat.

Lemma is_univalent_pointed_functor_cat
  : is_univalent pointed_functor_cat.
Proof.
  apply (is_univalent_total_category (is_univalent_functor_category _ _ is_univalent_HSET)).
  apply is_univalent_disp_iff_fibers_are_univalent.
  do 3 intro.
  use isweq_iso.
  - exact pr1.
  - intro.
    apply setproperty.
  - intro.
    apply z_iso_eq.
    apply setproperty.
Qed.

Lemma is_univalent_algebraic_theory_data_cat
  : is_univalent algebraic_theory_data_cat.
Proof.
  apply (is_univalent_total_category is_univalent_pointed_functor_cat).
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros T comp comp'.
  use isweq_iso.
  - intro f.
    do 4 (apply funextsec; intro).
    apply (pr1 f _).
  - intro.
    prove_hlevel.
    refine (_ : isofhlevel _ (∏ m, _)).
    prove_hlevel.
  - intro.
    apply z_iso_eq.
    prove_hlevel.
    refine (_ : isofhlevel _ (∏ m, _)).
    prove_hlevel.
Qed.

Lemma is_univalent_algebraic_theory_cat
  : is_univalent algebraic_theory_cat.
Proof.
  apply (is_univalent_total_category is_univalent_algebraic_theory_data_cat).
  apply disp_full_sub_univalent.
  exact isaprop_is_algebraic_theory.
Qed.

Definition algebraic_theory_univalent_category
  : univalent_category
  := make_univalent_category _ is_univalent_algebraic_theory_cat.
