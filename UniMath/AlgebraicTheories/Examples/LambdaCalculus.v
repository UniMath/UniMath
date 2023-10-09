Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.Tuples.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.

Section LambdaCalculus.

Variable L : lambda_calculus.

Definition lambda_calculus_algebraic_theory_data
  : algebraic_theory'_data
  := make_algebraic_theory'_data
    L
    (λ _, var)
    (λ _ _ l targets, subst l targets).

Lemma lambda_calculus_is_algebraic_theory
  : is_algebraic_theory' lambda_calculus_algebraic_theory_data.
Proof.
  use make_is_algebraic_theory'.
  - do 4 intro.
    apply subst_var.
  - unfold comp_identity_projections, comp'.
    use (lambda_calculus_ind_prop (λ _ _, _ ,, _));
      simpl.
    + apply setproperty.
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
  - unfold comp_is_assoc, comp'.
    intros l m n f_l f_m f_n.
    revert l f_l m f_m n f_n.
    use (lambda_calculus_ind_prop (λ _ _, _ ,, _));
      simpl.
    + do 4 (apply impred; intro).
      apply setproperty.
    + intros.
      now do 2 rewrite subst_var.
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
        rewrite subst_var.
        exact (!extend_tuple_inl _ _ _).
      * rewrite extend_tuple_inr, subst_var.
        exact (!extend_tuple_inr _ _).
    + intros m n l f Hl Hf m' f_m' n' f_n'.
      rewrite Hl.
      do 2 rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hf.
Qed.

Definition lambda_calculus_algebraic_theory
  : algebraic_theory
  := make_algebraic_theory' _ lambda_calculus_is_algebraic_theory.

Definition lambda_calculus_lambda_theory_data
  : lambda_theory_data.
Proof.
  refine (lambda_calculus_algebraic_theory ,, _ ,, _);
    simpl.
  - intros ? l.
    exact (app (inflate l) (var lastelement)).
  - intro.
    exact abs.
Defined.

Definition lambda_calculus_is_lambda_theory
  : is_lambda_theory lambda_calculus_lambda_theory_data.
Proof.
  repeat split;
    intros;
    cbn;
    unfold extend_finite_morphism_with_identity, inflate.
  - rewrite subst_subst, subst_app, subst_var, subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    apply (maponpaths (λ x, _ x _)).
    apply maponpaths.
    apply funextfun.
    intro.
    now rewrite subst_var, subst_var, (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
  - rewrite subst_abs.
    do 2 apply maponpaths.
    refine (!extend_tuple_eq _ _).
    + intro.
      refine (_ @ maponpaths _ (!extend_tuple_inl _ _ _)).
      apply inflate_var.
    + exact (maponpaths _ (!extend_tuple_inr _ _)).
  - rewrite subst_app, subst_subst, subst_subst, subst_var, subst_var, (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    apply (maponpaths (λ x, _ x _)).
    apply maponpaths.
    apply funextfun.
    intro.
    now rewrite subst_var, (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
  - rewrite subst_abs.
    do 2 apply maponpaths.
    apply extend_tuple_eq.
    + intro.
      refine (!extend_tuple_inl _ _ _).
    + rewrite subst_var.
      exact (!extend_tuple_inr _ _).
Qed.

Definition lambda_calculus_lambda_theory
  : lambda_theory
  := _ ,, lambda_calculus_is_lambda_theory.

Lemma lambda_calculus_has_eta
  : has_eta lambda_calculus_lambda_theory.
Proof.
  unfold has_eta.
  intros n l.
  apply eta_equality.
Qed.

Lemma lambda_calculus_has_beta
  : has_beta lambda_calculus_lambda_theory.
Proof.
  unfold has_beta, LambdaTheories.app, LambdaTheories.abs.
  simpl.
  intros n l.
  repeat reduce_lambda.
  rewrite subst_subst.
  refine (_ @ subst_l_var _).
  apply maponpaths.
  apply funextfun.
  intro i.
  unfold extend_tuple.
  refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
  induction (invmap stnweq i) as [i' | i'];
    simpl;
    repeat reduce_lambda.
  - apply extend_tuple_inl.
  - apply extend_tuple_inr.
Qed.

End LambdaCalculus.
