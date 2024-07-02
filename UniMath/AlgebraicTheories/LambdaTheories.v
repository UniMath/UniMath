(**************************************************************************************************

  λ-theories

  A λ-theory is a model for the untyped λ-calculus. It is a structure with variables, substitution,
  abstraction and application. Here it is formalized as an algebraic theory L, with functions
  between the L n and L (S n) that are compatible with the substitution in some way.
  This file defines what a λ-theory is and gives accessors, constructors and defines what it means
  for a λ-theory to have β- and η-equality.

  Contents
  1. The definition of λ-theories [lambda_theory]
  2. The definition of β-equality [has_β]
  3. The definiiton of η-equality [has_η]
  4. Lemmas on the interaction of abs with subst [subst_abs] [inflate_abs]
  5. The definition and properties of app and beta_equality [app] [subst_app] [beta_equality]
  6. A characterization of app and abs in terms of app' and one
    [app_from_app'] [abs_from_one]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategoryCore.

Local Open Scope algebraic_theories.

(** * 1. The definition of λ-theories *)

Definition lambda_theory_data : UU
  := lambda_theory_data_cat.

Definition make_lambda_theory_data
  (T : algebraic_theory)
  (app : ∏ n f, app_ax T n f)
  (abs : ∏ n f, abs_ax T n f)
  : lambda_theory_data
  := T ,, app ,, abs.

#[reversible=no] Coercion lambda_theory_data_to_algebraic_theory (L : lambda_theory_data)
  : algebraic_theory
  := pr1 L.

Definition appx {L : lambda_theory_data} {n : nat} (f : L n) : app_ax L n f := pr12 L n f.

Definition abs {L : lambda_theory_data} {n : nat} (f : L (S n)) : abs_ax L n f := pr22 L n f.

Definition lambda_theory : UU := lambda_theory_cat.

Definition extended_composition
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T (S m))
  (g : stn m → T n)
  : T (S n)
  := f • (extend_tuple (λ i, inflate (g i)) (var (stnweq (inr tt)))).

Definition app_subst_ax
  (L : lambda_theory_data)
  (m n : nat)
  (f : L m)
  (g : stn m → L n)
  : UU
  := appx (f • g) = extended_composition (appx f) g.

Arguments app_subst_ax /.

Definition abs_subst_ax
  (L : lambda_theory_data)
  (m n : nat)
  (f : L (S m))
  (g : stn m → L n)
  : UU
  := abs (extended_composition f g) = abs f • g.

Arguments abs_subst_ax /.

Definition is_lambda_theory (L : lambda_theory_data) : UU :=
  (∏ m n f g, app_subst_ax L m n f g) ×
  (∏ m n f g, abs_subst_ax L m n f g).

Definition make_is_lambda_theory
  {L : lambda_theory_data}
  (app_subst : ∏ m n f g, app_subst_ax L m n f g)
  (abs_subst : ∏ m n f g, abs_subst_ax L m n f g)
  : is_lambda_theory L
  := app_subst ,, abs_subst.

Definition make_lambda_theory
  (L : lambda_theory_data)
  (H : is_lambda_theory L)
  : lambda_theory
  := L ,, H.

#[reversible=no] Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data := pr1 L.

Definition app_subst
  (L : lambda_theory)
  {m n : nat}
  (f : L m)
  (g : stn m → L n)
  : app_subst_ax (L : lambda_theory_data) m n f g
  := pr12 L m n f g.

Definition abs_subst
  (L : lambda_theory)
  {m n : nat}
  (f : L (S m))
  (g : stn m → L n)
  : abs_subst_ax (L : lambda_theory_data) m n f g
  := pr22 L m n f g.

(** * 2. The definition of β-equality *)

Definition has_β (L : lambda_theory) : UU
  := ∏ n l, β_ax L n l.

Lemma isaprop_has_β
  (L : lambda_theory)
  : isaprop (has_β L).
Proof.
  do 2 (apply impred; intro).
  apply setproperty.
Qed.

(** * 3. The definiiton of η-equality *)

Definition has_η (L : lambda_theory) : UU
  := ∏ n l, η_ax L n l.

Lemma isaprop_has_η
  (L : lambda_theory)
  : isaprop (has_η L).
Proof.
  do 2 (apply impred; intro).
  apply setproperty.
Qed.

(** * 4. Lemmas on the interaction of abs with subst *)

Definition subst_abs (L : lambda_theory) {m n : nat} (f : L (S m)) (g : stn m → L n)
  : subst (abs f) g = abs (subst f (extend_tuple (λ i, inflate (g i)) (var (stnweq (inr tt)))))
  := !abs_subst _ _ _.

Definition inflate_abs (L : lambda_theory) {n : nat} (f : L (S n))
  : inflate (abs f) = abs (subst f (extend_tuple (λ i, var (stnweq (inl (stnweq (inl i))))) (var (stnweq (inr tt))))).
Proof.
  unfold inflate.
  rewrite subst_abs.
  apply (maponpaths (λ x, abs (f • extend_tuple x _))).
  apply funextfun.
  intro i.
  apply inflate_var.
Qed.

(** * 5. The definition and properties of app and beta_equality *)

Definition app {L : lambda_theory_data} {n : nat} (f g : L n) : L n
  := appx f • extend_tuple var g.

Lemma appx_to_app
  {L : lambda_theory}
  {n : nat}
  (f : L n)
  : appx f = app (inflate f) (var (stnweq (inr tt))).
Proof.
  symmetry.
  refine (maponpaths (λ x, x • _) (app_subst _ _ _) @ _).
  refine (subst_subst _ (appx _) _ _ @ _).
  refine (_ @ subst_var _ _).
  apply maponpaths.
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - refine (maponpaths (λ x, x • _) (extend_tuple_inl _ _ _) @ _).
    refine (subst_inflate _ _ _ @ _).
    refine (var_subst _ _ _ @ _).
    apply extend_tuple_inl.
  - refine (maponpaths (λ x, x • _) (extend_tuple_inr _ _ _) @ _).
    refine (var_subst _ _ _ @ _).
    apply extend_tuple_inr.
Qed.

Lemma subst_app (L : lambda_theory) {m n : nat} (f g : L m) (h : stn m → L n)
  : subst (app f g) h = app (subst f h) (subst g h).
Proof.
  unfold subst, app.
  rewrite app_subst.
  unfold extended_composition.
  do 2 rewrite (subst_subst _ (appx f)).
  apply maponpaths.
  apply funextfun.
  intro i.
  rewrite <- (homotweqinvweq stnweq i).
  induction (invmap stnweq i) as [i' | i'].
  - do 2 rewrite extend_tuple_inl.
    rewrite var_subst.
    rewrite subst_inflate.
    refine (!subst_var _ _ @ _).
    apply maponpaths.
    apply funextfun.
    intro j.
    now rewrite extend_tuple_inl.
  - do 2 rewrite extend_tuple_inr.
    rewrite var_subst.
    now rewrite extend_tuple_inr.
Qed.

Definition inflate_app (L : lambda_theory) {n : nat} (f g : L n)
  : inflate (app f g) = app (inflate f) (inflate g)
  := subst_app L _ _ _.

Definition beta_equality (L : lambda_theory) (H : has_β L) {n : nat} (f : L (S n)) (g : L n)
  : app (abs f) g = subst f (extend_tuple var g).
Proof.
  unfold app, abs.
  now rewrite H.
Qed.

Declare Scope lambda_calculus.
  Notation "( a b )" := (app a b) (only printing) : lambda_calculus.
  Notation "(π m )" := (var (make_stn _ m (idpath true))) (only printing) : lambda_calculus.
  Notation "(λ' n , x )" := (@abs _ n x) (only printing) : lambda_calculus.
Close Scope lambda_calculus.

(** * 6. A characterization of app and abs in terms of app' and one *)

Definition app'
  (L : lambda_theory_data)
  : (L 2 : hSet)
  := appx (var (n := 1) (● 0)%stn).

Definition one
  (L : lambda_theory_data)
  : (L 0 : hSet)
  := abs (abs (appx (var (n := 1) (● 0)%stn))).

Section AppAbs.

  Context (L : lambda_theory).
  Context (H : has_β L).

  Lemma app_from_app'
    {n : nat}
    (s : (L n : hSet))
    : appx s = extended_composition (app' L) (λ _, s).
  Proof.
    exact (!maponpaths _ (var_subst _ _ _) @ app_subst _ _ _).
  Qed.

  Local Lemma aux1
    {n : nat}
    {s : (L (S n) : hSet)}
    {t : (L n : hSet)}
    (H2 : extended_composition (app' L) (λ _ : (⟦ 1 ⟧)%stn, t) = s)
    : abs s = app' L • extend_tuple (λ _ : (⟦ 1 ⟧)%stn, lift_constant n (one L)) t.
  Proof.
    refine (!maponpaths _ H2 @ _).
    refine (abs_subst _ _ _ @ _).
    refine (!maponpaths (λ x, x • _) (H _ _) @ _).
    refine (maponpaths (λ x, x • _) (app_from_app' (one L)) @ _).
    refine (subst_subst _ (app' L) _ _ @ _).
    apply maponpaths.
    refine (!extend_tuple_eq _ _).
    - intro i'.
      refine (!_ @ !maponpaths (λ x, x • _) (extend_tuple_inl _ _ _)).
      refine (subst_subst _ (one L) _ _ @ _).
      apply (maponpaths (subst _)).
      apply (pr2 (iscontr_empty_tuple _)).
    - refine (!_ @ !maponpaths (λ x, x • _) (extend_tuple_inr _ _ _)).
      apply var_subst.
  Qed.

  Lemma abs_from_one
    {n : nat}
    (s : (L (S n) : hSet))
    (t : (L n : hSet))
    : abs s = t
    ≃ (app' L • extend_tuple (λ _, lift_constant _ (one L)) t = t)
      × (extended_composition (app' L) (λ _, t) = s).
  Proof.
    use (logeqweq
      (make_hProp _ (setproperty _ _ _))
      (make_hProp _ (isapropdirprod _ _ (setproperty _ _ _) (setproperty _ _ _)))).
    - intro H1.
      assert (H2 : extended_composition (app' L) (λ _, t) = s).
      {
        refine (!app_from_app' _ @ _).
        refine (!maponpaths _ H1 @ _).
        apply H.
      }
      refine (make_dirprod _ H2).
      refine (_ @ H1).
      exact (!aux1 H2).
    - intro H'.
      induction H' as [H1 H2].
      refine (_ @ H1).
      exact (aux1 H2).
  Qed.

End AppAbs.
