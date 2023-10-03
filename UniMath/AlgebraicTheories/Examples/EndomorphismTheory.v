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

Definition Terminal_is_empty_product
  {C : category}
  (T : Terminal C)
  (c : stn 0 → C)
  : Product (stn 0) C c.
Proof.
  use make_Product.
  - exact (TerminalObject T).
  - abstract (
      intro i;
      apply fromempty;
      exact (negnatlthn0 _ (stnlt i))
    ).
  - use make_isProduct.
    + apply homset_property.
    + intros.
      use make_iscontr.
      * use tpair.
        -- apply (TerminalArrow T).
        -- abstract (
            intro i;
            apply fromempty;
            exact (negnatlthn0 _ (stnlt i))
          ).
      * abstract (
          intro t;
          use subtypePairEquality;
          [ intro i;
            apply impred_isaprop;
            intro;
            apply homset_property
          | apply (TerminalArrowUnique T) ]
        ).
Defined.

Definition n_power_to_sn_power
  {C : category}
  (BP : BinProducts C)
  (n : nat)
  (c : C)
  (P : Product (stn n) C (λ _, c))
  : Product (stn (S n)) C (λ _, c).
Proof.
  use ((_ ,, _) ,, _).
  - exact (BP c P).
  - intro i.
    induction (invmap stnweq i) as [i' | i'].
    + exact (
        BinProductPr2 _ _ ·
        ProductPr _ _ _ i'
      ).
    + apply BinProductPr1.
  - intros c' cone'.
    use ((_ ,, _) ,, _).
    + use BinProductArrow.
      * apply (cone' (stnweq (inr tt))).
      * apply ProductArrow.
        intro i.
        apply (cone' (stnweq (inl i))).
    + abstract (
        intro i;
        refine (_ @ maponpaths _ (homotweqinvweq stnweq i));
        simpl;
        induction (invmap (Y := stn (S n)) stnweq i) as [i' | i'];
        [ simpl;
          rewrite assoc;
          rewrite BinProductPr2Commutes;
          apply (ProductPrCommutes _ _ _ P)
        | rewrite (BinProductPr1Commutes _ _ _ (BP c P));
          apply maponpaths;
          now apply stn_eq ]
      ).
    + abstract (
        intro t;
        apply subtypePairEquality;
        [ intro;
          apply impred_isaprop;
          intro;
          apply homset_property
        | apply BinProductArrowUnique;
          [ refine (!_ @ pr2 t _);
            apply maponpaths;
            exact (maponpaths _ (homotinvweqweq _ _))
          | apply ProductArrowUnique;
            intro i;
            refine (_ @ pr2 t _);
            refine (assoc' _ _ _ @ _);
            refine (maponpaths _ (!_));
            exact (maponpaths _ (homotinvweqweq _ _)) ] ]
      ).
Defined.

Definition bin_product_power
  (C : category)
  (c : C)
  (T : Terminal C)
  (BP : BinProducts C)
  (n : nat)
  : Product (stn n) C (λ _, c).
Proof.
  induction n.
  - exact (Terminal_is_empty_product T _).
  - apply (n_power_to_sn_power BP _ _ IHn).
Defined.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Context (C_terminal : Terminal C).
  Context (C_bin_products : BinProducts C).

  Variable (X : C).

  Definition power
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
    use make_is_lambda_theory'; simpl.
    - intros m n f g.
      refine (maponpaths _ (assoc' _ _ _) @ _).
      refine (φ_adj_inv_natural_precomp (pr2 E) _ _ _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply BinProductArrow_eq.
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq _ _) @ _).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (maponpaths _ (_ : _ = inr tt)).
        now apply invmap_eq.
      + do 2 refine (bp_commutes_2 _ _ _ _ @ !_).
        apply ProductArrow_eq.
        intro i.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (pow_commutes _ _ _ _) @ !_).
        refine (pow_commutes _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq _ _) @ _).
        apply (maponpaths (λ x, x · _)).
        apply ProductArrow_eq.
        intro j.
        refine (pow_commutes _ _ _ _ @ _).
        refine (maponpaths _ (_ : _ = inl j)).
        apply invmap_eq.
        exact (!eqtohomot (replace_dni_last _) j).
    - intros m n f g.
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (φ_adj_natural_precomp (pr2 E) _ _ _ _ _)).
      apply (maponpaths (λ x, _ (x · _) · _)).
      apply ProductArrow_eq.
      intro.
      refine (pow_commutes _ _ _ _ @ !_).
      unfold ProductPr.
      refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
      simpl.
      induction (invmap (Y := stn (S m)) stnweq i).
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (bp_commutes_2 _ _ _ _) @ _).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (pow_commutes _ _ _ _) @ !_).
        refine (maponpaths _ (homotinvweqweq _ (inl a)) @ _).
        apply (maponpaths (λ x, x · _)).
        apply ProductArrow_eq.
        intro.
        refine (pow_commutes _ _ _ _ @ _).
        refine (maponpaths _ (_ : _ = inl i0)).
        apply invmap_eq.
        exact (!eqtohomot (replace_dni_last _) i0).
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (maponpaths _ (homotinvweqweq _ (inr tt)) @ _).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq _ (inr tt))).
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
    cbn.
    rewrite φ_adj_after_φ_adj_inv.
    rewrite assoc'.
    rewrite abs_after_app.
    apply id_right.
  Qed.

End EndomorphismAlgebraicTheory.

Definition set_endomorphism_theory
  (X : hSet)
  : algebraic_theory
  := endomorphism_theory (TerminalHSET) BinProductsHSET (X : ob HSET).
