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

  Now, given categories C and C', with chosen objects X and X', if a functor F: C → C' sends X to X'
  and preserves the binary product and terminal element, we obtain a λ-theory morphism between the
  endomorphism theories.

  Contents
  1. The definition of the endomorphism algebraic theory [endomorphism_theory]
  2. The definition of the endomorphism λ-theory [endomorphism_lambda_theory]
  3. A characterization of the endomorphism theories with β-equality [endomorphism_theory_has_β]
  4. A characterization of the endomorphism theories with η-equality [endomorphism_theory_has_eta]
  5. The endomorphism theory of a set [set_endomorphism_theory]
  6. The morphism between endomorphism theories [functor_to_lambda_theory_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
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

  Definition endomorphism_theory_data : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - intro n.
      exact (homset (power n) X).
    - intro.
      apply ProductPr.
    - intros m n f g.
      exact (f ∘ (ProductArrow _ _ _ g)).
  Defined.

  Definition endomorphism_is_theory : is_algebraic_theory endomorphism_theory_data.
  Proof.
    use make_is_algebraic_theory.
    - intros l m n f_l f_m f_n.
      simpl.
      refine (assoc _ _ _ @ _).
      apply (maponpaths (λ f, f · f_l)).
      rewrite (ProductArrowEta _ _ _ _ _ (_ · _)).
      apply maponpaths, funextfun.
      intro.
      rewrite assoc'.
      refine (maponpaths _ _).
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - do 4 intro.
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - do 2 intro.
      simpl.
      rewrite <- id_left.
      apply (maponpaths (λ x, x · _)).
      rewrite (ProductArrowEta _ _ _ _ _ (identity _)).
      apply maponpaths, funextfun.
      intro.
      exact (!id_left _).
  Qed.

  Definition endomorphism_theory : algebraic_theory
    := make_algebraic_theory _ endomorphism_is_theory.

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
    use make_is_lambda_theory.
    - intros m n f g.
      refine (maponpaths _ (assoc' _ _ _) @ _).
      refine (φ_adj_inv_natural_precomp (pr2 E) _ _ _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply BinProductArrowsEq.
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (bp_commutes_1 _ _ _ _ @ _).
        refine (extend_tuple_inr _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq _ (inr tt))).
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
        exact (maponpaths _ (homotinvweqweq _ (inl j))).
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
        exact (maponpaths _ (homotinvweqweq _ (inl j))).
      + refine (bp_commutes_1 _ _ _ _ @ _).
        refine (id_right _ @ !_).
        refine (extend_tuple_inr _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq _ (inr tt))).
  Qed.

  Definition endomorphism_lambda_theory
    : lambda_theory
    := make_lambda_theory _ endomorphism_theory_is_lambda.

(** * 3. A characterization of the endomorphism theories with β-equality *)

  Lemma endomorphism_theory_has_β
    (app_after_abs : abs · app = identity _)
    : has_β endomorphism_lambda_theory.
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
    : has_η endomorphism_lambda_theory.
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

Section Morphism.

  Context {C C' : category}.

  Context (C_terminal : Terminal C).
  Context (C_bin_products : BinProducts C).
  Context (X : C).

  Context (C'_terminal : Terminal C').
  Context (C'_bin_products : BinProducts C').
  Context (X' : C').

  Context (E : is_exponentiable C_bin_products X).
  Context (abs : C⟦pr1 E X, X⟧).
  Context (app : C⟦X, pr1 E X⟧).
  Context (C_beta : abs · app = identity _).

  Context (E' : is_exponentiable C'_bin_products X').
  Context (abs' : C'⟦pr1 E' X', X'⟧).
  Context (app' : C'⟦X', pr1 E' X'⟧).
  Context (C'_beta : abs' · app' = identity _).

  Let L := endomorphism_lambda_theory C_terminal C_bin_products X E abs app.
  Let L' := endomorphism_lambda_theory C'_terminal C'_bin_products X' E' abs' app'.

  Context (F : C ⟶ C').
  Context (F_preserves_X : z_iso (F X) X').
  Context (F_preserves_terminal : preserves_terminal F).
  Context (F_preserves_binproduct : preserves_binproduct F).

  Let power
    (n : nat)
    : Product (stn n) C (λ _, X)
    := bin_product_power C X C_terminal C_bin_products n.

  Let power'
    (n : nat)
    : Product (stn n) C' (λ _, X')
    := bin_product_power C' X' C'_terminal C'_bin_products n.

  Definition F_power_iso
    (n : nat)
    : z_iso (F (power n)) (power' n).
  Proof.
    induction n as [ | n IHn].
    - apply (z_iso_Terminals (make_Terminal _ (F_preserves_terminal _ (pr2 C_terminal))) C'_terminal).
    - refine (z_iso_comp (preserves_binproduct_to_z_iso _ F_preserves_binproduct _ (C'_bin_products _ _)) _).
      apply binproduct_of_z_iso.
      + exact F_preserves_X.
      + exact IHn.
  Defined.

  Lemma F_preserves_power_pr
    {n : nat}
    (i : stn n)
    : #F (ProductPr _ _ (power n) i)
      = F_power_iso n · ProductPr _ _ (power' n) i · inv_from_z_iso F_preserves_X.
  Proof.
    induction n as [ | n IHn].
    - induction (negnatlthn0 _ (stnlt i)).
    - rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, # F(_ x)) (homotinvweqweq stnweq _) @ !_);
        refine (maponpaths (λ x, _ · _ x · _) (homotinvweqweq stnweq _) @ !_).
      + refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
        refine (_ @ maponpaths (λ x, x · _ · _) (assoc _ _ _)).
        refine (_ @ !maponpaths (λ x, _ · x · _ · _) (BinProductOfArrowsPr2 _ _ _ _ _)).
        refine (_ @ maponpaths (λ x, x · _ · _) (assoc' _ _ _)).
        refine (_ @ !maponpaths (λ x, x · _ · _ · _) (BinProductPr2Commutes _ _ _ _ _ _ _)).
        refine (functor_comp _ _ _ @ _).
        refine (maponpaths _ (IHn _) @ _).
        refine (assoc _ _ _ @ _).
        exact (maponpaths (λ x, x · _) (assoc _ _ _)).
      + cbn.
        refine (_ @ maponpaths (λ x, x · _) (assoc _ _ _)).
        refine (_ @ !maponpaths (λ x, _ x · _) (BinProductOfArrowsPr1 _ _ _ _ _)).
        refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
        refine (_ @ assoc _ _ _).
        refine (_ @ !maponpaths _ (z_iso_inv_after_z_iso _)).
        refine (_ @ !id_right _).
        exact (!BinProductPr1Commutes _ _ _ _ _ _ _).
  Qed.

  Lemma F_preserves_product_arrow
    {n : nat}
    (Y : C)
    (f : stn n → C⟦Y, X⟧)
    : #F (ProductArrow _ _ (power n) f)
      = ProductArrow _ _ (power' n) (λ i, #F (f i) · F_preserves_X) · inv_from_z_iso (F_power_iso n).
  Proof.
    apply z_iso_inv_on_left.
    apply ProductArrow_eq.
    intro i.
    refine (!_ @ assoc _ _ _).
    refine (!maponpaths _ ((z_iso_inv_to_right _ _ _ _ _ _ (F_preserves_power_pr _))) @ _).
    refine (assoc _ _ _ @ _).
    refine (!maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
    refine (maponpaths (λ x, #F x · _) (ProductPrCommutes _ _ _ _ _ _ _) @ !_).
    exact (ProductPrCommutes _ _ _ _ _ _ _).
  Qed.

  Definition functor_to_algebraic_theory_morphism_data
    : algebraic_theory_morphism_data L L'
    := λ _ f, inv_from_z_iso (F_power_iso _) · #F f · F_preserves_X.

  Lemma functor_to_is_algebraic_theory_morphism
    : is_algebraic_theory_morphism functor_to_algebraic_theory_morphism_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - intros n i.
      refine (maponpaths (λ x, _ · x · _) (F_preserves_power_pr _) @ _).
      apply z_iso_inv_to_right.
      apply z_iso_inv_on_right.
      apply assoc'.
    - intros m n f g.
      refine (assoc' _ _ _ @ _).
      apply z_iso_inv_on_right.
      do 2 refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
      apply (maponpaths (λ x, x · _)).
      refine (functor_comp _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      refine (F_preserves_product_arrow _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      apply ProductArrow_eq.
      intro i.
      refine (ProductPrCommutes _ _ _ _ _ _ _ @ !_).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (z_iso_inv_after_z_iso _) @ _).
      exact (maponpaths (λ x, x · _) (id_left _)).
  Qed.

  Definition functor_to_algebraic_theory_morphism
    : algebraic_theory_morphism L L'
    := make_algebraic_theory_morphism _ functor_to_is_algebraic_theory_morphism.

  Context (F_preserves_E : z_iso (F (pr1 E X)) (pr1 E' X')).
  Context (F_preserves_φ_adj_inv
    : #F (φ_adj_inv (pr2 E) app)
    = preserves_binproduct_to_z_iso _ F_preserves_binproduct (C_bin_products _ _) (C'_bin_products _ _)
      · binproduct_of_z_iso _ _ F_preserves_X F_preserves_X
      · φ_adj_inv (pr2 E') app'
      · inv_from_z_iso F_preserves_X).

  Context (F_preserves_φ_adj
    : #F (φ_adj (pr2 E) (var (T := L) (● 0 : stn 1)%stn))
    = preserves_terminal_to_z_iso _ F_preserves_terminal C_terminal _
      · φ_adj (pr2 E') (var (T := L') (● 0 : stn 1)%stn)
      · inv_from_z_iso F_preserves_E).

  Context (F_preserves_app_abs_abs
    : #F (# (pr1 E) (app · abs) · abs)
    = F_preserves_E
      · # (pr1 E') (app' · abs') · abs'
      · inv_from_z_iso F_preserves_X).

  Lemma functor_to_morphism_preserves_app'
    : preserves_app' functor_to_algebraic_theory_morphism.
  Proof.
    refine (maponpaths _ (φ_adj_inv_natural_precomp _ _ _ _ _ _) @ !_).
    refine (φ_adj_inv_natural_precomp (pr2 E') _ _ _ _ _ @ !_).
    refine (maponpaths (λ x, _ · x · _) (functor_comp _ _ _) @ _).
    apply z_iso_inv_to_right.
    apply z_iso_inv_on_right.
    refine (maponpaths (λ x, _ · x) F_preserves_φ_adj_inv @ _).
    do 2 refine (assoc _ _ _ @ !_).
    apply (maponpaths (λ x, x · _)).
    do 2 refine (assoc _ _ _ @ !_).
    apply (maponpaths (λ x, x · _)).
    refine (maponpaths (λ x, x · _) (preserves_binproduct_to_preserves_arrow _ F_preserves_binproduct _ (C'_bin_products _ _) _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ · x · _) (z_iso_after_z_iso_inv _) @ _).
    refine (maponpaths (λ x, x · _) (id_right _) @ _).
    apply BinProductArrowsEq;
      do 2 refine (assoc' _ _ _ @ !_).
    - do 2 refine (maponpaths _ (BinProductOfArrowsPr1 _ _ _ _ _) @ !_).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (BinProductPr1Commutes _ _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (preserves_binproduct_to_preserves_pr1 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, _ · x · _) (functor_id _ _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ !_).

      refine (maponpaths _ (id_right _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths (λ x, _ · x) (BinProductPr1Commutes _ _ _ _ _ _ _) @ _).
      exact (assoc _ _ _).
    - do 2 refine (maponpaths _ (BinProductOfArrowsPr2 _ _ _ _ _) @ !_).
      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _).
      refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
      refine (maponpaths (λ x, x · _ · _) (preserves_binproduct_to_preserves_pr2 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, _ · x · _) (preserves_binproduct_to_preserves_pr1 _ F_preserves_binproduct _ (C'_bin_products _ _)) @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ !_).

      refine (assoc _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _).
      refine (maponpaths (λ x, _ · x · _) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _).
      do 2 refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (maponpaths _ (BinProductOfArrowsPr1 _ _ _ _ _) @ _).
      exact (assoc _ _ _).
  Qed.

  Lemma functor_to_morphism_preserves_one
    : preserves_one functor_to_algebraic_theory_morphism.
  Proof.
    refine (maponpaths (λ x, _ (_ (x · _) · _)) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (maponpaths (λ x, _ (_ x · _)) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ (x · _)) (φ_adj_natural_postcomp _ _ _ _ _ _) @ _).
    refine (maponpaths _ (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, _ · x · _) (functor_comp _ _ _) @ _).
    refine (maponpaths (λ x, _ · (x · _) · _) F_preserves_φ_adj @ _).
    refine (assoc' _ _ _ @ !_).
    refine (maponpaths (λ x, _ (x · _) · _) (φ_adj_after_φ_adj_inv _ _) @ _).
    refine (maponpaths (λ x, _ x · _) (assoc' _ _ _) @ _).
    refine (maponpaths (λ x, x · _) (φ_adj_natural_postcomp _ _ _ _ _ _) @ !_).
    apply z_iso_inv_on_right.
    do 3 refine (assoc' _ _ _ @ _).
    apply (maponpaths (λ x, _ · x)).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (λ x, φ_adj (pr2 E') (var (T := L') (● 0 : stn 1)%stn) · x)).
    apply z_iso_inv_on_right.
    refine (_ @ assoc' _ _ _).
    apply z_iso_inv_to_right.
    apply F_preserves_app_abs_abs.
  Qed.

  Lemma functor_to_is_lambda_theory_morphism
    : is_lambda_theory_morphism functor_to_algebraic_theory_morphism.
  Proof.
    use make_is_lambda_theory_morphism'.
    - use endomorphism_theory_has_β.
      exact C_beta.
    - use endomorphism_theory_has_β.
      exact C'_beta.
    - exact functor_to_morphism_preserves_app'.
    - exact functor_to_morphism_preserves_one.
  Qed.

  Definition functor_to_lambda_theory_morphism
    : lambda_theory_morphism L L'
    := make_lambda_theory_morphism
      functor_to_algebraic_theory_morphism
      functor_to_is_lambda_theory_morphism.

End Morphism.
