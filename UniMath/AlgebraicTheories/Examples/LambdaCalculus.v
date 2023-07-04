Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.

Local Open Scope vec.

Definition extend_tuple
  {T : nat → UU}
  {m n : nat}
  (upgrade : T n → T (S n))
  (last : T (S n))
  (f : stn m → T n)
  : stn (S m) → T (S n).
Proof.
  intro i.
  induction (invweq (weqdnicoprod _ lastelement) i).
  - exact (upgrade (f a)).
  - exact last.
Defined.

Lemma extend_tuple_dni_lastelement
  {T : nat → UU}
  {m n : nat}
  (upgrade : T n → T (S n))
  (last : T (S n))
  (f : stn m → T n)
  (i : stn m)
  : extend_tuple
    upgrade
    last
    f
    (dni_lastelement i)
  = upgrade (f i).
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod m lastelement) (dni_lastelement i) = inl i); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod m lastelement)).
  refine (homotweqinvweq _ _ @ maponpaths (λ x, x i) (!replace_dni_last _)).
Qed.

Lemma extend_tuple_lastelement
  {T : nat → UU}
  {m n : nat}
  (upgrade : T n → T (S n))
  (last : T (S n))
  (f : stn m → T n)
  : extend_tuple
    upgrade
    last
    f
    lastelement
  = last.
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod m lastelement) lastelement = inr tt); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod m lastelement)).
  exact (homotweqinvweq _ _).
Qed.

Lemma extend_tuple_eq
  {T : nat → UU}
  {m n : nat}
  {upgrade : T n → T (S n)}
  {last : T (S n)}
  {f : stn m → T n}
  {g : stn (S m) → T (S n)}
  (Hf : ∏ i, upgrade (f i) = g (dni_lastelement i))
  (Hlast : last = g lastelement)
  : extend_tuple upgrade last f = g.
Proof.
  apply funextfun.
  intro i.
  refine ((idpath _ : (_ = coprod_rect _ _ _ (invmap _ _))) @ _ @ maponpaths g (homotweqinvweq (weqdnicoprod m lastelement) i)).
  induction (invmap (weqdnicoprod m lastelement) i).
  - exact (Hf a @ maponpaths (λ x, g (x a)) (!replace_dni_last _)).
  - exact Hlast.
Qed.

Section LambdaCalculus.

Variable lambda_calculus : nat → hSet.
Variable var : ∏ n, stn n → lambda_calculus n.
Variable app : ∏ n, lambda_calculus n → lambda_calculus n → lambda_calculus n.
Variable abs : ∏ n, lambda_calculus (S n) → lambda_calculus n.

Variable lambda_calculus_ind : ∏
  (A : ∏ n (l : lambda_calculus n), UU)
  (f_var : ∏ n i, A _ (var n i))
  (f_app : ∏ n l l', A _ l → A _ l' → A _ (app n l l'))
  (f_abs : ∏ n l, A _ l → A _ (abs n l))
  , (∏ n l, A n l).

Variable lambda_calculus_ind_var
  : ∏ {A f_var f_app f_abs n} i, lambda_calculus_ind A f_var f_app f_abs n (var _ i) = f_var _ i.

Variable lambda_calculus_ind_app
  : ∏ {A f_var f_app f_abs n} l l', lambda_calculus_ind A f_var f_app f_abs n (app _ l l') = f_app _ _ _ (lambda_calculus_ind _ f_var f_app f_abs _ l) (lambda_calculus_ind _ f_var f_app f_abs _ l').

Variable lambda_calculus_ind_abs
  : ∏ {A f_var f_app f_abs n} l, lambda_calculus_ind A f_var f_app f_abs n (abs _ l) = f_abs _ _ (lambda_calculus_ind _ f_var f_app f_abs _ l).

Definition lambda_calculus_rect : ∏
  (A : nat → UU)
  (f_var : ∏ n, stn n → A n)
  (f_app : ∏ n, A n → A n → A n)
  (f_abs : ∏ n, A (S n) → A n)
  , (∏ n, lambda_calculus n → A n)
  := λ A f_var f_app f_abs,
    lambda_calculus_ind
    (λ n _, A n)
    f_var
    (λ n _ _, f_app n)
    (λ n _, f_abs n).

Lemma lambda_calculus_rect_var
  : ∏ {A f_var f_app f_abs n} i, lambda_calculus_rect A f_var f_app f_abs n (var _ i) = f_var _ i.
Proof.
  intros.
  use lambda_calculus_ind_var.
Qed.

Lemma lambda_calculus_rect_app
  : ∏ {A f_var f_app f_abs n} l l', lambda_calculus_rect A f_var f_app f_abs n (app _ l l') = f_app _ (lambda_calculus_rect _ f_var f_app f_abs _ l) (lambda_calculus_rect _ f_var f_app f_abs _ l').
Proof.
  intros.
  use lambda_calculus_ind_app.
Qed.

Lemma lambda_calculus_rect_abs
  : ∏ {A f_var f_app f_abs n} l, lambda_calculus_rect A f_var f_app f_abs n (abs _ l) = f_abs _ (lambda_calculus_rect _ f_var f_app f_abs _ l).
Proof.
  intros.
  use lambda_calculus_ind_abs.
Qed.

(* A thing to think about *)

Definition inflate
  {n : nat}
  (l : lambda_calculus n)
  : lambda_calculus (S n)
  := lambda_calculus_rect _ (λ _ i, (var _ (dni_lastelement i))) (λ _, app _) (λ _, abs _) n l.

Lemma inflate_var
  {n : nat}
  {i : stn n}
  : inflate (var _ i) = var _ (dni_lastelement i).
Proof.
  exact (lambda_calculus_rect_var i).
Qed.

Lemma inflate_app
  {n : nat}
  {l l' : lambda_calculus n}
  : inflate (app _ l l') = app _ (inflate l) (inflate l').
Proof.
  exact (lambda_calculus_rect_app l l').
Qed.

Lemma inflate_abs
  {n : nat}
  {l : lambda_calculus (S n)}
  : inflate (abs _ l) = abs _ (inflate l).
Proof.
  exact (lambda_calculus_rect_abs l).
Qed.

Definition substitute
  {m n : nat}
  (targets : stn m → lambda_calculus n)
  (l : lambda_calculus m)
  : lambda_calculus n
  := lambda_calculus_rect
    (λ _, (∏ n, _ → lambda_calculus n))
    (λ _ i _ targets, targets i)
    (λ _ f g _ targets, app _ (f _ targets) (g _ targets))
    (λ _ f _ targets, abs _ (f _ (extend_tuple (T := lambda_calculus) inflate (var _ lastelement) targets)))
    _ l n targets.

Lemma substitute_var
  {m n : nat}
  (targets : stn m → lambda_calculus n)
  (i : stn m)
  : substitute targets (var _ i) = targets i.
Proof.
  exact (maponpaths (λ x, x _ _) (lambda_calculus_rect_var i)).
Qed.

Lemma substitute_app
  {m n : nat}
  (targets : stn m → lambda_calculus n)
  (l l' : lambda_calculus m)
  : substitute targets (app _ l l') = (app _ (substitute targets l) (substitute targets l')).
Proof.
  exact (maponpaths (λ x, x _ _) (lambda_calculus_rect_app l l')).
Qed.

Lemma substitute_abs
  {m n : nat}
  (targets : stn m → lambda_calculus n)
  (l : lambda_calculus (S m))
  : substitute targets (abs _ l) = (abs _ (substitute (extend_tuple (T := lambda_calculus) inflate (var _ lastelement) targets) l)).
Proof.
  exact (maponpaths (λ x, x _ _) (lambda_calculus_rect_abs l)).
Qed.

Definition lambda_calculus_theory_data
  : algebraic_theory'_data
  := make_algebraic_theory'_data
    lambda_calculus
    var
    (λ _ _ l targets, substitute targets l).

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
      apply (maponpaths (λ x, _ x _)).
      refine (extend_tuple_eq _ (idpath _)).
      exact (λ i, lambda_calculus_rect_var i).
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
      apply maponpaths.
      apply (maponpaths (λ x, _ x _)).
      refine (!extend_tuple_eq _ _).
      * intro i.
        rewrite extend_tuple_dni_lastelement.
        revert n f_n.
        refine (lambda_calculus_ind (λ _ f_m, ∏ n f_n, inflate (substitute f_n f_m) = substitute _ (inflate (f_m))) _ _ _ _ (f_m i));
        clear m f_m i.
        -- intros.
          rewrite inflate_var.
          do 2 rewrite substitute_var.
          exact (!extend_tuple_dni_lastelement _ _ _ _).
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
