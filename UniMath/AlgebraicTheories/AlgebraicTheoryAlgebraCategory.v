Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebraMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition algebraic_theory_algebra_data_full_disp_cat
  : disp_cat (cartesian algebraic_theory_cat HSET).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : hSet).
    exact (∏ n, (T n : hSet) → (stn n → A) → A).
  - intros X X' action action' Y.
    pose (A := make_algebraic_theory_algebra_data (pr2 X) action).
    pose (A' := make_algebraic_theory_algebra_data (pr2 X') action').
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : A → A').
    exact (∏ n f a, G (action n f a) = action' n (F _ f) (λ i, G (a i))).
  - intros.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - intros X action n f a.
    pose (A := pr2 X : hSet).
    assert (H : pr2 (identity X) = identity (A : HSET)).
    + apply (eqtohomot (transportf_const _ (A → A))).
    + now rewrite H.
  - intros X X' X'' action action' action'' y y' Gcommutes G'commutes n f a.
    pose (A := pr2 X : hSet).
    pose (A' := pr2 X' : hSet).
    pose (A'' := pr2 X'' : hSet).
    pose (G := pr2 y : A → A').
    pose (G' := pr2 y' : A' → A'').
    assert (H : pr2 (y · y') = (G : HSET⟦A, A'⟧) · G').
    + apply (eqtohomot (transportf_const _ (A → A''))).
    + rewrite H.
      unfold compose.
      simpl.
      now rewrite Gcommutes, G'commutes.
Defined.

Definition algebraic_theory_algebra_data_full_cat : category
  := total_category algebraic_theory_algebra_data_full_disp_cat.

Definition algebraic_theory_algebra_full_disp_cat
  : disp_cat algebraic_theory_algebra_data_full_cat
  := disp_full_sub algebraic_theory_algebra_data_full_cat
    (λ X, is_algebraic_theory_algebra (make_algebraic_theory_algebra_data (pr21 X) (pr2 X))).

Definition algebraic_theory_algebra_full_cat : category
  := total_category algebraic_theory_algebra_full_disp_cat.

Definition algebraic_theory_algebra_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat algebraic_theory_algebra_full_disp_cat).

Definition algebraic_theory_algebra_cat
  (T : algebraic_theory)
  := fiber_category algebraic_theory_algebra_disp_cat T.

Lemma displayed_algebra_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {A : algebraic_theory_algebra T}
  {A' : algebraic_theory_algebra T'}
  (G G' : (A : algebraic_theory_algebra_disp_cat _) -->[F] A')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  apply (subtypePairEquality' H).
  use (isapropdirprod _ _ _ isapropunit).
  repeat (apply impred_isaprop; intro).
  apply setproperty.
Qed.

Lemma is_univalent_disp_algebraic_theory_algebra_data_full_disp_cat
  : is_univalent_disp algebraic_theory_algebra_data_full_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro f.
    do 3 (apply funextsec; intro).
    pose (H := pr1 f x x0 x1).
    cbn in H.
    unfold transportb in H.
    rewrite (transportf_set _ _ _ (isasetaprop (isasetunit _ _))) in H.
    exact H.
  - intro.
    do 3 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 3 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Lemma is_univalent_algebraic_theory_algebra_data_full_cat
  : is_univalent algebraic_theory_algebra_data_full_cat.
Proof.
  use is_univalent_total_category.
  - rewrite cartesian_is_binproduct.
    exact (is_univalent_category_binproduct is_univalent_algebraic_theory_cat is_univalent_HSET).
  - exact is_univalent_disp_algebraic_theory_algebra_data_full_disp_cat.
Qed.

Lemma is_univalent_disp_algebraic_theory_algebra_full_disp_cat
  : is_univalent_disp algebraic_theory_algebra_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_is_algebraic_theory_algebra _).
Qed.

Lemma is_univalent_algebraic_theory_algebra_full_cat
  : is_univalent algebraic_theory_algebra_full_cat.
Proof.
  apply (is_univalent_total_category is_univalent_algebraic_theory_algebra_data_full_cat).
  exact is_univalent_disp_algebraic_theory_algebra_full_disp_cat.
Qed.

Lemma is_univalent_algebraic_theory_algebra_cat (T : algebraic_theory)
  : is_univalent (algebraic_theory_algebra_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  unfold algebraic_theory_algebra_disp_cat.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_reindex_disp_cat.
    refine (pr2 (is_univalent_disp_iff_fibers_are_univalent _) _).
    intros c a b.
    (* Copied from HSET/Univalence *)
    assert (idtoiso (a := a) (b := b) = pr1 (hset_id_weq_z_iso a b)).
    {
      apply funextfun.
      intro p.
      induction p.
      apply z_iso_eq.
      apply funextfun.
      now intro.
    }
    rewrite X.
    apply hset_id_weq_z_iso.
  - exact is_univalent_disp_algebraic_theory_algebra_data_full_disp_cat.
  - exact is_univalent_disp_algebraic_theory_algebra_full_disp_cat.
Qed.
