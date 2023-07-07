Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.Tuples.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.

Section LambdaCalculus.

Variable L : lambda_calculus.

Definition lambda_calculus_theory_data
  : algebraic_theory'_data
  := make_algebraic_theory'_data
    L
    (λ _, var)
    (λ _ _ l targets, subst l targets).

Lemma lambda_calculus_is_theory
  : is_algebraic_theory' lambda_calculus_theory_data.
Proof.
  use make_is_algebraic_theory'.
  - do 4 intro.
    apply subst_var.
  - unfold comp_identity_projections.
    cbn.
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
  - unfold comp_is_assoc.
    cbn.
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
      * intro i.
        rewrite extend_tuple_dni_lastelement.
        rewrite inflate_subst.
        unfold inflate.
        rewrite subst_subst.
        apply maponpaths.
        apply funextfun.
        intro.
        now rewrite subst_var, extend_tuple_dni_lastelement.
      * now rewrite extend_tuple_lastelement, subst_var, extend_tuple_lastelement.
    + intros m n l f Hl Hf m' f_m' n' f_n'.
      rewrite Hl.
      do 2 rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      now rewrite Hf.
Qed.

Definition lambda_theory
  : algebraic_theory
  := make_algebraic_theory' _ lambda_calculus_is_theory.

End LambdaCalculus.
