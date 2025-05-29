(**

  The λ-calculus λ-theory

  Given a model for the λ-calculus, this file constructs a λ-theory and shows that it has
  eta and beta equality (since we assume that the λ-calculus has these equalities).

  Contents
  1. The algebraic theory of the λ-calculus [lambda_calculus_algebraic_theory]
  2. The λ-theory of the λ-calculus [lambda_calculus_lambda_theory]
  3. The λ-theory has β-equality [lambda_calculus_has_β]
  4. The λ-theory is the initial λ-theory with β-equality [lambda_calculus_is_initial]

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.

(** * 1. The algebraic theory of the λ-calculus *)

Section LambdaCalculus.

Variable L : lambda_calculus.

Definition lambda_calculus_algebraic_theory_data
  : algebraic_theory_data
  := make_algebraic_theory_data
    L
    (λ _, var)
    (λ _ _ l targets, subst l targets).

Lemma lambda_calculus_is_algebraic_theory
  : is_algebraic_theory lambda_calculus_algebraic_theory_data.
Proof.
  use make_is_algebraic_theory.
  - intros l m n f_l f_m f_n.
    revert l f_l m f_m n f_n.
    use (lambda_calculus_ind_prop (λ _ _, _ ,, _));
      cbn -[isaprop].
    + do 4 (apply impred; intro).
      apply setproperty.
    + intros.
      now do 2 rewrite var_subst.
    + intros ? ? ? Hl Hl' ? ? ? ?.
      do 3 rewrite subst_app.
      now rewrite Hl, Hl'.
    + intros l f_l Hl m f_m n f_n.
      do 3 rewrite subst_abs.
      rewrite Hl.
      do 2 apply maponpaths.
      refine (!extend_tuple_eq _ _).
      * intro.
        refine (_ @ !maponpaths (λ x, subst x _) (extend_tuple_inl _ _ _)).
        rewrite inflate_subst.
        unfold inflate.
        rewrite subst_subst.
        apply maponpaths.
        apply funextfun.
        intro.
        now rewrite var_subst, extend_tuple_inl.
      * now rewrite extend_tuple_inr, var_subst, extend_tuple_inr.
    + intros m n l f Hl Hf m' f_m' n' f_n'.
      rewrite Hl.
      do 2 rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hf.
  - do 4 intro.
    apply var_subst.
  - use (lambda_calculus_ind_prop (λ _ _, make_hProp _ (setproperty _ _ _)));
      cbn.
    + intros.
      apply subst_var.
    + intros ? ? ? Hl Hl'.
      now rewrite subst_app, Hl, Hl'.
    + intros n' l Hl.
      rewrite subst_abs.
      apply maponpaths.
      refine (_ @ Hl).
      apply maponpaths.
      exact (extend_tuple_eq inflate_var (idpath _)).
    + intros ? ? ? ? Hl Hf.
      rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hf. (* Apparently we don't need Hl in this proof *)
Qed.

Definition lambda_calculus_algebraic_theory
  : algebraic_theory
  := make_algebraic_theory _ lambda_calculus_is_algebraic_theory.

(** * 2. The λ-theory of the λ-calculus *)

Definition lambda_calculus_lambda_theory_data
  : lambda_theory_data.
Proof.
  refine (lambda_calculus_algebraic_theory ,, _ ,, _);
    simpl.
  - intros ? l.
    exact (app (inflate l) (var (stnweq (inr tt)))).
  - intro.
    exact abs.
Defined.

Lemma lambda_calculus_app_is_app
  {n : nat}
  (f g : lambda_calculus_lambda_theory_data n)
  : LambdaTheories.app f g = LambdaCalculus.app f g.
Proof.
  cbn.
  rewrite subst_app.
  rewrite var_subst.
  rewrite subst_inflate.
  refine (maponpaths _ (extend_tuple_inr _ _ tt) @ _).
  apply (maponpaths (λ x, LambdaCalculus.app x _)).
  refine (_ @ subst_var _).
  apply maponpaths.
  apply funextfun.
  intro i.
  apply extend_tuple_inl.
Qed.

Definition lambda_calculus_is_lambda_theory
  : is_lambda_theory lambda_calculus_lambda_theory_data.
Proof.
  apply make_is_lambda_theory;
    do 4 intro;
    cbn -[stnweq];
    unfold inflate.
  - rewrite subst_app.
    do 2 rewrite subst_subst.
    rewrite var_subst.
    rewrite extend_tuple_inr.
    apply (maponpaths (λ x, _ (_ x) _)).
    apply funextfun.
    intro.
    now rewrite var_subst, extend_tuple_inl.
  - now rewrite subst_abs.
Qed.

Definition lambda_calculus_lambda_theory
  : lambda_theory
  := _ ,, lambda_calculus_is_lambda_theory.

(** * 3. The λ-theory has β-equality *)

Lemma lambda_calculus_has_β
  : has_β lambda_calculus_lambda_theory.
Proof.
  unfold has_β, LambdaTheories.app, LambdaTheories.abs.
  cbn -[stnweq].
  intros n l.
  rewrite inflate_abs.
  rewrite beta_equality.
  rewrite subst_subst.
  refine (_ @ subst_var _).
  apply maponpaths.
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - rewrite extend_tuple_inl.
    do 2 rewrite inflate_var.
    rewrite var_subst.
    now rewrite extend_tuple_inl.
  - rewrite extend_tuple_inr.
    rewrite var_subst.
    now rewrite extend_tuple_inr.
Qed.

Definition lambda_calculus_β_lambda_theory
  : β_lambda_theory
  := make_β_lambda_theory lambda_calculus_lambda_theory lambda_calculus_has_β.

(** * 4. The λ-calculus is the initial λ-theory with β-equality *)

Section Initial.

  Context (L' : β_lambda_theory).

  Definition lambda_calculus_initial_morphism_data
    : ∏ n, lambda_calculus_β_lambda_theory n → L' n.
  Proof.
    use (lambda_calculus_rect L').
    - exact (λ n, AlgebraicTheories.var).
    - exact (λ n, LambdaTheories.app).
    - exact (λ n, LambdaTheories.abs).
    - exact (λ m n, AlgebraicTheories.subst).
    - repeat split.
      + exact (λ m n, AlgebraicTheories.var_subst L').
      + exact (λ m n, LambdaTheories.subst_app L').
      + exact (λ m n, LambdaTheories.subst_abs L').
      + exact (λ l m n, AlgebraicTheories.subst_subst L').
      + exact (λ n, LambdaTheories.beta_equality L' (β_lambda_theory_has_β L')).
  Defined.

  Lemma lambda_calculus_initial_is_algebraic_theory_morphism
    : is_algebraic_theory_morphism lambda_calculus_initial_morphism_data.
  Proof.
    apply make_is_algebraic_theory_morphism.
    - exact (λ n, lambda_calculus_rect_var).
    - exact (λ m n, lambda_calculus_rect_subst).
  Qed.

  Definition lambda_calculus_initial_algebraic_theory_morphism
    : algebraic_theory_morphism lambda_calculus_β_lambda_theory L'
    := make_algebraic_theory_morphism _ lambda_calculus_initial_is_algebraic_theory_morphism.

  Lemma lambda_calculus_initial_is_lambda_theory_morphism
    : is_lambda_theory_morphism lambda_calculus_initial_algebraic_theory_morphism.
  Proof.
    use (make_is_lambda_theory_morphism).
    - intros n f.
      refine (_ @ !appx_to_app _).
      refine (lambda_calculus_rect_app _ _ @ _).
      refine (maponpaths (λ x, LambdaTheories.app _ x) (lambda_calculus_rect_var _) @ _).
      apply (maponpaths (λ x, LambdaTheories.app x _)).
      refine (lambda_calculus_rect_subst _ _ @ _).
      apply (maponpaths (AlgebraicTheories.subst _)).
      apply funextfun.
      intro i.
      apply lambda_calculus_rect_var.
    - exact (λ n, lambda_calculus_rect_abs).
  Qed.

  Definition lambda_calculus_initial_lambda_theory_morphism
    : lambda_theory_morphism lambda_calculus_β_lambda_theory L'
    := make_lambda_theory_morphism _ lambda_calculus_initial_is_lambda_theory_morphism.

  Definition lambda_calculus_initial_morphism
    : β_lambda_theory_morphism lambda_calculus_β_lambda_theory L'
    := make_β_lambda_theory_morphism lambda_calculus_initial_lambda_theory_morphism.

  Lemma lambda_calculus_initial_morphism_unique
    (f : β_lambda_theory_morphism lambda_calculus_β_lambda_theory L')
    : f = lambda_calculus_initial_morphism.
  Proof.
    apply β_lambda_theory_morphism_eq.
    apply lambda_theory_morphism_eq.
    apply algebraic_theory_morphism_eq.
    use (lambda_calculus_ind_prop (λ n t, make_hProp _ (setproperty _ _ _))).
    - intros n i.
      now do 2 refine (mor_var _ _ @ ! _).
    - intros n l l' Hl Hl'.
      do 2 refine (!_ @ maponpaths _ (lambda_calculus_app_is_app _ _)).
      do 2 refine (mor_app _ _ _ @ !_).
      exact (maponpaths_2 _ Hl _ @ maponpaths _ Hl').
    - intros n l Hl.
      do 2 refine (mor_abs _ _ @ !_).
      apply maponpaths.
      apply Hl.
    - intros mm n l l' Hl Hl'.
      do 2 refine (mor_subst _ _ _ @ !_).
      refine (maponpaths_2 _ Hl _ @ _).
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hl'.
  Qed.

  Definition lambda_calculus_unique_morphism
    : iscontr (β_lambda_theory_morphism lambda_calculus_β_lambda_theory L')
    := make_iscontr
      (make_β_lambda_theory_morphism lambda_calculus_initial_lambda_theory_morphism)
      lambda_calculus_initial_morphism_unique.

End Initial.

Definition lambda_calculus_is_initial
  : isInitial β_lambda_theory_cat lambda_calculus_β_lambda_theory
  := lambda_calculus_unique_morphism.

Definition initial_lambda_calculus
  : Initial β_lambda_theory_cat
  := make_Initial
    lambda_calculus_β_lambda_theory
    lambda_calculus_is_initial.

End LambdaCalculus.
