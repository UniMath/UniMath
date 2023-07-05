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
    (λ _ _ l targets, substitute l targets).

Lemma lambda_calculus_is_theory
  : is_algebraic_theory' lambda_calculus_theory_data.
Proof.
  use make_is_algebraic_theory'.
  - do 4 intro.
    apply substitute_var.
  - unfold comp_identity_projections.
    cbn.
    apply lambda_calculus_ind.
    + intros.
      apply substitute_var.
    + intros ? ? ? Hl Hl'.
      now rewrite substitute_app, Hl, Hl'.
    + intros n' l Hl.
      rewrite substitute_abs.
      apply maponpaths.
      refine (_ @ Hl).
      apply maponpaths.
      exact (extend_tuple_eq inflate_var (idpath _)).
  - unfold comp_is_assoc.
    cbn.
    intros l m n f_l f_m f_n.
    revert l f_l m f_m n f_n.
    refine (lambda_calculus_ind _ _ _ _).
    + intros.
      now do 2 rewrite substitute_var.
    + intros ? ? ? Hl Hl' ? ? ? ?.
      do 3 rewrite substitute_app.
      now rewrite Hl, Hl'.
    + intros l f_l Hl m f_m n f_n.
      do 3 rewrite substitute_abs.
      rewrite Hl.
      do 2 apply maponpaths.
      refine (!extend_tuple_eq _ _).
      * intro i.
        rewrite extend_tuple_dni_lastelement.
        revert n f_n.
        refine (lambda_calculus_ind (λ _ f_m, ∏ n f_n, inflate (substitute f_m f_n) = substitute (inflate f_m) _) _ _ _ _ (f_m i));
          clear m f_m i.
        -- intros.
          now rewrite inflate_var, substitute_var, substitute_var, extend_tuple_dni_lastelement.
        -- intros ? ? ? Hf_m Hf_m' ? ?.
          now rewrite substitute_app, inflate_app, inflate_app, substitute_app, Hf_m, Hf_m'.
        -- intros m f_m Hf_m n f_n.
          now rewrite substitute_abs, inflate_abs, inflate_abs, substitute_abs, Hf_m.
      * now rewrite extend_tuple_lastelement, substitute_var, extend_tuple_lastelement.
Qed.

Definition lambda_theory
  : algebraic_theory
  := make_algebraic_theory' _ lambda_calculus_is_theory.

End LambdaCalculus.
