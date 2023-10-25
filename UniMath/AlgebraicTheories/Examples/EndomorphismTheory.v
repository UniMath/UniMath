(**************************************************************************************************

  Endomorphism Theory

  Algebraic theories and λ-theories describe objects with "variables" and a substitution operation.
  An important class of examples are the so-called "endomorphism theories". Given an object X in a
  category with products, the endomorphism theory of X is the algebraic theory T with T(n) the set
  of morphisms from X^n to X with the projections as variables, where substitution of
  g1, …, gm: X^n → X into f: X^m → X creates the composite morphism X^n → X^m → X.
  One of the places where the endomorphism theory shows up, is in Scott's representation theorem,
  which shows that every model for the λ-calculus arises as the endomorphism theory of some object
  in some category.
  If X is also exponentiable and we have morphisms between X and X^X, we can turn X into a lambda
  theory.

  Contents
  1. The definition of the endomorphism algebraic theory [endomorphism_theory]
  2. The definition of the endomorphism λ-theory [endomorphism_lambda_theory]
  3. A characterization of the endomorphism theories with β-equality [endomorphism_theory_has_beta]
  4. A characterization of the endomorphism theories with η-equality [endomorphism_theory_has_eta]
  5. The endomorphism theory of a set [set_endomorphism_theory]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope cat.

(** * 1. The definition of the endomorphism algebraic theory *)

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context (C_terminal : Terminal C).
  Context (C_bin_products : BinProducts C).

  Variable (X : C).

  Let power
    (n : nat)
    : Product (stn n) C (λ _, X)
    := bin_product_power C X C_terminal C_bin_products n.

  Definition endomorphism_theory'_data : algebraic_theory'_data.
  Proof.
    use make_algebraic_theory'_data.
    - intro n.
      exact (homset (power n) X).
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

  (** * 2. The definition of the endomorphism λ-theory *)

  Let pow_commutes (n : nat) (c : C) (f : stn n → C⟦c, X⟧) (i : stn n)
    : ProductArrow _ _ (power n) f · ProductPr _ _ (power n) i = f i
    := (ProductPrCommutes _ _ _ (power n)) c f i.

  Let bp_commutes_1 (n : nat) (c : C) (f : C⟦c, X⟧) (g : C⟦c, power n⟧)
    : BinProductArrow _ (C_bin_products X (power n)) f g · BinProductPr1 _ _ = f
    := BinProductPr1Commutes _ _ _ (C_bin_products X (power n)) c f g.

  Let bp_commutes_2 (n : nat) (c : C) (f : C⟦c, X⟧) (g : C⟦c, power n⟧)
    : BinProductArrow _ (C_bin_products X (power n)) f g · BinProductPr2 _ _ = g
    := BinProductPr2Commutes _ _ _ (C_bin_products X (power n)) c f g.

  Context (E : is_exponentiable C_bin_products X).
  Context (abs : C⟦pr1 E X, X⟧).
  Context (app : C⟦X, pr1 E X⟧).

  Let hom_weq (n: nat)
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

  Lemma endomorphism_theory_is_lambda
    : is_lambda_theory endomorphism_lambda_theory_data.
  Proof.
    use make_is_lambda_theory'.
    - intros m n f g.
      refine (maponpaths _ (assoc' _ _ _) @ _).
      refine (φ_adj_inv_natural_precomp (pr2 E) _ _ _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply BinProductArrowsEq.
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
      apply (maponpaths (λ x, φ_adj (pr2 E) (x · _) · _)).
      apply ProductArrow_eq.
      intro i.
      refine (pow_commutes _ _ _ _ @ !_).
      rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, _ · (_ x)) (homotinvweqweq stnweq _) @ _).
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

(** * 3. A characterization of the endomorphism theories with β-equality *)

  Lemma endomorphism_theory_has_beta
    (app_after_abs : abs · app = identity _)
    : has_beta endomorphism_lambda_theory.
  Proof.
    intros n l.
    refine (_ @ φ_adj_inv_after_φ_adj (pr2 E) _).
    apply (maponpaths (φ_adj_inv _)).
    refine (assoc' _ _ _ @ _).
    refine (_ @ id_right _).
    apply maponpaths.
    exact app_after_abs.
  Qed.

(** * 4. A characterization of the endomorphism theories with η-equality *)

  Lemma endomorphism_theory_has_eta
    (abs_after_app : app · abs = identity _)
    : has_eta endomorphism_lambda_theory.
  Proof.
    intros n l.
    refine (maponpaths (λ x, x · _) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (_ @ id_right _).
    apply maponpaths.
    exact abs_after_app.
  Qed.

End EndomorphismAlgebraicTheory.

(** * 5. The endomorphism theory of a set *)

Definition set_endomorphism_theory
  (X : hSet)
  : algebraic_theory
  := endomorphism_theory (TerminalHSET) BinProductsHSET (X : ob HSET).
