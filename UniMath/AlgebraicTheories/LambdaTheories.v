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
  4. A characterization of app and abs in terms of app' and one
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

Definition app {L : lambda_theory_data} {n : nat} (f : L n) : app_ax L n f := pr12 L n f.

Definition abs {L : lambda_theory_data} {n : nat} (f : L (S n)) : abs_ax L n f := pr22 L n f.

Definition lambda_theory : UU := lambda_theory_cat.

Definition make_is_lambda_theory
  {L : lambda_theory_data}
  (app_comp : ∏ m n f g, app_comp_ax L m n f g)
  (abs_comp : ∏ m n f g, abs_comp_ax L m n f g)
  : is_lambda_theory L
  := app_comp ,, abs_comp.

Definition make_lambda_theory
  (L : lambda_theory_data)
  (H : is_lambda_theory L)
  : lambda_theory
  := L ,, H.

#[reversible=no] Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data := pr1 L.

Definition app_comp
  (L : lambda_theory)
  {m n : nat}
  (f : L m)
  (g : stn m → L n)
  : app_comp_ax (L : lambda_theory_data) m n f g
  := pr12 L m n f g.

Definition abs_comp
  (L : lambda_theory)
  {m n : nat}
  (f : L (S m))
  (g : stn m → L n)
  : abs_comp_ax (L : lambda_theory_data) m n f g
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

(** * 4. A characterization of app and abs in terms of app' and one *)

Definition app'
  (L : lambda_theory_data)
  : (L 2 : hSet)
  := app (pr (n := 1) (● 0)%stn).

Definition one
  (L : lambda_theory_data)
  : (L 0 : hSet)
  := abs (abs (app (pr (n := 1) (● 0)%stn))).

Section AppAbs.

  Context (L : lambda_theory).
  Context (H : has_β L).

  Lemma app_from_app'
    {n : nat}
    (s : (L n : hSet))
    : app s = extended_composition (app' L) (λ _, s).
  Proof.
    exact (!maponpaths _ (pr_comp _ _ _) @ app_comp _ _ _).
  Qed.

  Local Lemma aux1
    {n : nat}
    {s : (L (S n) : hSet)}
    {t : (L n : hSet)}
    (H2 : extended_composition (app' L) (λ _ : (⟦ 1 ⟧)%stn, t) = s)
    : abs s = app' L • extend_tuple (λ _ : (⟦ 1 ⟧)%stn, lift_constant n (one L)) t.
  Proof.
    refine (!maponpaths _ H2 @ _).
    refine (abs_comp _ _ _ @ _).
    refine (!maponpaths (λ x, x • _) (H _ _) @ _).
    refine (maponpaths (λ x, x • _) (app_from_app' (one L)) @ _).
    refine (comp_comp L (app' L) _ _ @ _).
    apply maponpaths.
    refine (!extend_tuple_eq _ _).
    - intro i'.
      refine (!_ @ !maponpaths (λ x, (_ x) • _) (homotinvweqweq stnweq _)).
      refine (comp_comp L (one L) _ _ @ _).
      apply (maponpaths (comp _)).
      apply funextfun.
      intro i.
      induction (negnatlthn0 _ (stnlt i)).
    - refine (!_ @ !maponpaths (λ x, (_ x) • _) (homotinvweqweq stnweq _)).
      apply pr_comp.
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
