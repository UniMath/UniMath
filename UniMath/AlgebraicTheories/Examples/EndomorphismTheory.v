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
  Context (C_finite_products : finite_products C).
  Variable (X : C).

  Definition endomorphism_theory'_data : algebraic_theory'_data.
  Proof.
    use make_algebraic_theory'_data.
    - intro n.
      pose (power := ProductObject _ _ (C_finite_products n (λ _, X))).
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

  Context (BP : BinProducts C).

  Local Definition pow_commutes (n : nat)
    := (ProductPrCommutes _ _ _ (C_finite_products n (λ _, X))).

  Local Definition bp_commutes_1 (n : nat)
    := BinProductPr1Commutes _ _ _ (BP X (C_finite_products n (λ _, X))).

  Local Definition bp_commutes_2 (n : nat)
    := BinProductPr2Commutes _ _ _ (BP X (C_finite_products n (λ _, X))).

  Definition product_power
    (n : nat)
    : Product (⟦ S n ⟧)%stn C (λ _ : (⟦ S n ⟧)%stn, X).
  Proof.
    use ((_ ,, _) ,, _).
    - exact (BP X (C_finite_products n (λ _, X))).
    - simpl.
      use extend_tuple.
      + intro i.
        exact (
          (BinProductPr2 _ _) ·
          (ProductPr _ _ _ i)
        ).
      + apply BinProductPr1.
    - intros c' cone'.
      use ((_ ,, _) ,, _); cbn.
      + use (BinProductArrow _ (BP X _) _ _).
        * exact (cone' lastelement).
        * apply ProductArrow.
          intro i.
          exact (cone' (dni lastelement i)).
      + abstract (
          intro i;
          unfold extend_tuple;
          refine (_ @ maponpaths _ (homotweqinvweq (weqdnicoprod n lastelement) i));
          simpl;
          induction (invmap (weqdnicoprod n lastelement) i);
          [ simpl;
            rewrite assoc;
            rewrite bp_commutes_2;
            apply pow_commutes
          | apply bp_commutes_1 ]
        ).
      + abstract (
          intro t;
          apply subtypePairEquality';
          [ apply BinProductArrowUnique;
            [ refine (!_ @ pr2 t lastelement);
              apply maponpaths;
              apply extend_tuple_lastelement
            | apply ProductArrowUnique;
              intro i;
              rewrite <- (pr2 t (dni lastelement i));
              rewrite assoc';
              apply maponpaths;
              rewrite replace_dni_last;
              now rewrite extend_tuple_dni_lastelement]
          | apply impred_isaprop;
            intro;
            apply homset_property ]
        ).
  Defined.

  Context (E : is_exponentiable BP X).
  Context (abs : C⟦pr1 E X, X⟧).
  Context (app : C⟦X, pr1 E X⟧).

  Local Definition hom_weq (n: nat)
    : C⟦product_power n, X⟧ ≃ C⟦(C_finite_products n (λ _, X)), pr1 E X⟧
    := adjunction_hom_weq (pr2 E) _ _.

  Local Definition product_iso (n : nat)
    : iso (C_finite_products (S n) (λ _, X)) (product_power n)
    := invweq weq_iso_z_iso (z_iso_between_Product _ _).

  Definition endomorphism_lambda_theory_data
    : lambda_theory_data.
  Proof.
    use make_lambda_theory_data.
    - exact endomorphism_theory.
    - intros n f.
      pose (f' := f · app).
      refine (_ · invmap (hom_weq n) f').
      apply morphism_from_iso.
      apply product_iso.
    - intros n f.
      refine (_ · abs).
      apply hom_weq.
      refine (_ · f).
      apply inv_from_iso.
      apply product_iso.
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
      unfold LambdaTheories.app, endomorphism_lambda_theory_data.
      simpl.
      cbn.
      rewrite assoc'.
      rewrite φ_adj_inv_natural_precomp.
      simpl.
      do 2 rewrite assoc.
      apply (maponpaths (λ x, x · _)).
      unfold BinProduct_of_functors_mor, BinProductOfArrows.
      apply BinProductArrow_eq.
      * cbn.
        do 2 rewrite assoc'.
        rewrite id_right.
        do 2 rewrite (bp_commutes_1 m).
        rewrite (bp_commutes_1 n).
        rewrite pow_commutes.
        rewrite extend_tuple_lastelement.
        now rewrite pow_commutes.
      * cbn.
        do 2 rewrite replace_dni_last.
        do 2 rewrite assoc'.
        apply ProductArrow_eq.
        intro.
        rewrite (bp_commutes_2 m).
        rewrite assoc.
        do 2 rewrite bp_commutes_2.
        do 2 rewrite assoc'.
        do 4 rewrite pow_commutes.
        now rewrite extend_tuple_dni_lastelement.
    - intros m n f g.
      unfold LambdaTheories.abs, endomorphism_lambda_theory_data, comp'.
      cbn.
      unfold precomp_with.
      do 2 rewrite assoc.
      rewrite <- φ_adj_natural_precomp.
      cbn.
      unfold BinProduct_of_functors_mor, BinProductOfArrows.
      cbn.
      apply (maponpaths (λ x, _ (x) · _)).
      rewrite assoc.
      apply (maponpaths (λ x, x · _)).
      apply ProductArrow_eq.
      intro.
      do 3 rewrite id_right.
      do 2 rewrite assoc'.
      do 2 rewrite (pow_commutes (S m)).
      set (tmp := (extend_tuple (λ i0, BinProductPr2 _ _ · ProductPr _ _ (C_finite_products n (λ _, X)) i0) _)).
      unfold extend_tuple.
      induction (idpath _ : extend_tuple _ _ = tmp).
      simpl.
      induction (invmap (weqdnicoprod m lastelement) i).
      + cbn.
        do 2 rewrite assoc.
        rewrite bp_commutes_2.
        do 2 rewrite assoc'.
        rewrite (pow_commutes m).
        rewrite assoc.
        apply (maponpaths (λ x, x · _)).
        apply ProductArrow_eq.
        intro.
        rewrite assoc'.
        rewrite (pow_commutes n).
        rewrite (pow_commutes (S n)).
        now rewrite extend_tuple_dni_lastelement.
      + cbn.
        rewrite (pow_commutes 1).
        rewrite (pow_commutes (S n)).
        rewrite bp_commutes_1.
        now rewrite extend_tuple_lastelement.
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
    cbn -[ProductArrow product_iso].
    rewrite φ_adj_inv_after_φ_adj.
    rewrite assoc.
    rewrite (idpath _ : ProductArrow _ _ _ _ = morphism_from_iso (product_iso n)).
    rewrite iso_inv_after_iso.
    apply id_left.
  Qed.

  Lemma endomorphism_theory_has_eta
    (abs_after_app : app · abs = identity _)
    : has_eta endomorphism_lambda_theory.
  Proof.
    intros n l.
    unfold LambdaTheories.abs, LambdaTheories.app.
    simpl.
    rewrite assoc.
    rewrite (idpath _ : ProductArrow _ _ _ _ = morphism_from_iso (product_iso n)).
    rewrite iso_after_iso_inv.
    rewrite id_left.
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
  := endomorphism_theory (λ n, ProductsHSET (stn n)) (X : ob HSET).
