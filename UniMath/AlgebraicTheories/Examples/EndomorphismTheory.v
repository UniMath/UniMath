(*
  Defines the endomorphism theory of an object X in some category with products, given by
  T(n) = (X^n → X). Also gives a specialization for X a set.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.Tuples.

Local Open Scope cat.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context (C_terminal : Terminal C).
  Context (C_bin_products : BinProducts C).

  Variable (X : C).

  Local Definition power
    (n : nat)
    : Product (stn n) C (λ _, X)
    := bin_product_power C X C_terminal C_bin_products n.

  Definition endomorphism_theory'_data : algebraic_theory'_data.
  Proof.
    use make_algebraic_theory'_data.
    - intro n.
      pose (power := ProductObject _ _ (power n)).
      exact (homset power X).
    - intro.
      apply ProductPr.
    - intros m n f g.
      exact (f ∘ (ProductArrow _ _ _ g)).
  Defined.

  Definition endomorphism_is_theory' : is_algebraic_theory' endomorphism_theory'_data.
  Proof.
    use make_is_algebraic_theory'.
    - do 4 intro.
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - do 2 intro.
      rewrite <- id_left.
      apply (maponpaths (λ x, x · _)).
      rewrite (ProductArrowEta _ _ _ _ _ (identity _)).
      apply maponpaths, funextfun.
      intro.
      symmetry.
      apply id_left.
    - intros l m n f_l f_m f_n.
      unfold comp'.
      simpl.
      rewrite assoc.
      apply (maponpaths (λ f, f · f_l)).
      rewrite (ProductArrowEta _ _ _ _ _ (_ · _)).
      apply maponpaths, funextfun.
      intro.
      rewrite assoc'.
      apply maponpaths.
      exact (ProductPrCommutes _ _ _ _ _ _ _).
  Qed.

  Definition endomorphism_theory : algebraic_theory
    := make_algebraic_theory' _ endomorphism_is_theory'.

  Local Definition pow_commutes (n : nat)
    := (ProductPrCommutes _ _ _ (power n)).

  Local Definition bp_commutes_1 (n : nat)
    := BinProductPr1Commutes _ _ _ (C_bin_products X (power n)).

  Local Definition bp_commutes_2 (n : nat)
    := BinProductPr2Commutes _ _ _ (C_bin_products X (power n)).

  Context (E : is_exponentiable C_bin_products X).
  Context (abs : C⟦pr1 E X, X⟧).
  Context (app : C⟦X, pr1 E X⟧).

  Local Definition hom_weq (n: nat)
    : C⟦power (S n), X⟧ ≃ C⟦power n, pr1 E X⟧
    := adjunction_hom_weq (pr2 E) (power n) X.

  Definition endomorphism_lambda_theory_data
    : lambda_theory_data.
  Proof.
    use make_lambda_theory_data.
    - exact endomorphism_theory.
    - intros n f.
      exact (invmap (hom_weq n) (f · app)).
    - intros n f.
      exact (hom_weq n f · abs).
  Defined.

  Proposition BinProductArrow_eq
              {a b : C}
              (w : C)
              (x : BinProduct _ a b)
              (f g : w --> x)
              (Ha : f · BinProductPr1 _ x = g · BinProductPr1 _ x)
              (Hb : f · BinProductPr2 _ x = g · BinProductPr2 _ x)
    : f = g.
  Proof.
    refine (BinProductArrowEta _ _ _ _ _ _ @ _ @ !(BinProductArrowEta _ _ _ _ _ _)).
    now rewrite Ha, Hb.
  Qed.

  Lemma endomorphism_theory_is_lambda
    : is_lambda_theory endomorphism_lambda_theory_data.
  Proof.
    use make_is_lambda_theory'.
    - intros m n f g.
      refine (maponpaths _ (assoc' _ _ _) @ _).
      refine (φ_adj_inv_natural_precomp (pr2 E) _ _ _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply BinProductArrow_eq.
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (extend_tuple_inr _ _ @ _).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (extend_tuple_inr _ _).
      + do 2 refine (bp_commutes_2 _ _ _ _ @ !_).
        apply ProductArrow_eq.
        intro i.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (pow_commutes _ _ _ _) @ !_).
        refine (pow_commutes _ _ _ _ @ _).
        refine (extend_tuple_inl _ _ _ @ _).
        apply (maponpaths (λ x, x · _)).
        apply ProductArrow_eq.
        intro j.
        refine (pow_commutes _ _ _ _ @ _).
        refine (extend_tuple_inl _ _ _).
    - intros m n f g.
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (φ_adj_natural_precomp (pr2 E) _ _ _ _ _)).
      apply (maponpaths (λ x, _ (x · _) · _)).
      apply ProductArrow_eq.
      intro i.
      refine (pow_commutes _ _ _ _ @ !_).
      refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
      unfold ProductPr, stnweq.
      simpl.
      induction (invmap (Y := stn (S m)) (weqdnicoprod m lastelement) i) as [i' | i'].
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (bp_commutes_2 _ _ _ _) @ _).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (pow_commutes _ _ _ _) @ !_).
        refine (extend_tuple_inl _ _ _ @ _).
        apply (maponpaths (λ x, x · _)).
        apply ProductArrow_eq.
        intro j.
        refine (pow_commutes _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq _ (inl j))).
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (extend_tuple_inr _ _ @ _).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (extend_tuple_inr _ _).
  Qed.

  Definition endomorphism_lambda_theory
    : lambda_theory
    := make_lambda_theory _ endomorphism_theory_is_lambda.

  Lemma endomorphism_theory_has_beta
    (app_after_abs : abs · app = identity _)
    : has_beta endomorphism_lambda_theory.
  Proof.
    intros n l.
    unfold LambdaTheories.abs, LambdaTheories.app.
    simpl.
    rewrite assoc'.
    rewrite app_after_abs.
    rewrite id_right.
    apply (φ_adj_inv_after_φ_adj (pr2 E)).
  Qed.

  Lemma endomorphism_theory_has_eta
    (abs_after_app : app · abs = identity _)
    : has_eta endomorphism_lambda_theory.
  Proof.
    intros n l.
    unfold LambdaTheories.abs, LambdaTheories.app.
    refine (maponpaths (λ x, x · _) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (λ x, _ · x) abs_after_app @ _).
    apply id_right.
  Qed.

End EndomorphismAlgebraicTheory.

Definition set_endomorphism_theory
  (X : hSet)
  : algebraic_theory
  := endomorphism_theory (TerminalHSET) BinProductsHSET (X : ob HSET).
