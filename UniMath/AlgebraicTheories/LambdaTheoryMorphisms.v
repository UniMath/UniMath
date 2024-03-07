(**************************************************************************************************

  λ-theory morphisms

  Defines what a morphism of λ-theories is.

  Contents
  1. The definition of λ-theory morphisms [lambda_theory_morphism]
  2. An algebaic theory morphism is a λ-theory morphism if it preserves "app'" and "one"
    [make_is_lambda_theory_morphism']
  3. Under the right circumstances, preservation of app and abs follow from each other
    [has_eta_has_beta_preserves_app] [has_beta_has_eta_preserves_abs]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope algebraic_theories.
Local Open Scope cat.

(** * 1. The definition of λ-theory morphisms [lambda_theory_morphism] *)

Definition lambda_theory_morphism
  (L L' : lambda_theory)
  : UU
  := lambda_theory_cat⟦L, L'⟧.

Definition is_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : algebraic_theory_morphism L L')
  : UU
  := (∏ n f, mor_app_ax F n f) ×
    (∏ n f, mor_abs_ax F n f).

Definition make_lambda_theory_morphism
  {L L' : lambda_theory}
  (F : algebraic_theory_morphism L L')
  (H : is_lambda_theory_morphism F)
  : lambda_theory_morphism L L'
  := (F ,, H) ,, tt.

#[reversible=no] Coercion lambda_theory_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  : algebraic_theory_morphism L L'
  := pr11 F.

Definition mor_app
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  {n : nat}
  (f : L n)
  : mor_app_ax F n f
  := pr121 F n f.

Definition mor_abs
  {L L' : lambda_theory}
  (F : lambda_theory_morphism L L')
  {n : nat}
  (f : L (S n))
  : mor_abs_ax F n f
  := pr221 F n f.

Lemma lambda_theory_morphism_eq
  {L L' : lambda_theory}
  (F F' : lambda_theory_morphism L L')
  (H : (F : algebraic_theory_morphism L L') = F')
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropunit.
  }
  apply subtypePath.
  {
    intro.
    apply isapropdirprod;
      do 2 (apply impred_isaprop; intro);
      apply setproperty.
  }
  apply H.
Qed.

(** 2. An algebaic theory morphism is a λ-theory morphism if it preserves "app'" and "one" *)

Section MakeIsLambdaTheoryMorphism'.

  Context {L L' : lambda_theory}.
  Context (H : has_β L).
  Context (H' : has_β L').
  Context (F : algebraic_theory_morphism L L').

  Definition preserves_app'
    : UU
    := F _ (app' L) = app' L'.

  Definition preserves_one
    : UU
    := F _ (one L) = one L'.

  Lemma make_is_lambda_theory_morphism'
    (H1 : preserves_app')
    (H2 : preserves_one)
    : is_lambda_theory_morphism F.
  Proof.
    split.
    - intros n t.
      refine (maponpaths _ (app_from_app' _ _) @ !_).
      refine (app_from_app' _ _ @ !_).
      refine (mor_comp _ _ _ @ _).
      refine (maponpaths (λ x, x • _) H1 @ _).
      apply (maponpaths (comp _)).
      refine (!extend_tuple_eq _ _).
      + intro i.
        refine (!_ @ !maponpaths (λ x, _ (_ x)) (homotinvweqweq stnweq _)).
        refine (mor_comp _ _ _ @ _).
        apply maponpaths.
        apply funextfun.
        intro i'.
        apply mor_pr.
      + exact (!mor_pr _ _).
    - intros n t.
      induction (abs_from_one _ H t (abs t) (idpath _)) as [H3 H4].
      refine (!invmap (abs_from_one _ H' _ _) _).
      split.
      + refine (!_ @ maponpaths _ H3).
        refine (mor_comp _ _ _ @ _).
        refine (maponpaths (λ x, x • _) H1 @ !_).
        apply maponpaths.
        apply extend_tuple_eq.
        * intro i.
          refine (!_ @ !maponpaths (λ x, _ (_ x)) (homotinvweqweq stnweq _)).
          refine (mor_comp _ _ _ @ _).
          refine (maponpaths (λ x, x • _) H2 @ _).
          apply (maponpaths (comp _)).
          apply funextfun.
          intro j.
          induction (negnatlthn0 _ (stnlt j)).
        * now refine (!_ @ !maponpaths (λ x, _ (_ x)) (homotinvweqweq stnweq _)).
      + refine (!_ @ maponpaths _ H4).
        refine (mor_comp _ _ _ @ _).
        refine (maponpaths (λ x, x • _) H1 @ !_).
        apply (maponpaths (comp _)).
        apply extend_tuple_eq.
        * intro i.
          refine (!_ @ !maponpaths (λ x, _ (_ x)) (homotinvweqweq stnweq _)).
          refine (mor_comp _ _ _ @ _).
          apply maponpaths.
          apply funextfun.
          intro i'.
          apply mor_pr.
        * exact (!mor_pr _ _).
  Qed.

End MakeIsLambdaTheoryMorphism'.

(** 3. Under the right circumstances, preservation of app and abs follow from each other *)

Lemma has_eta_has_beta_preserves_app
  {L L' : lambda_theory}
  {F : algebraic_theory_morphism L L'}
  (HL : has_η L)
  (HL' : has_β L')
  (Habs : ∏ n l, mor_abs_ax F n l)
  (n : nat)
  (l : L n)
  : mor_app_ax F n l.
Proof.
  refine (!HL' _ _ @ _).
  refine (maponpaths _ (!Habs _ _) @ _).
  exact (maponpaths (λ x, _ (_ x)) (HL _ _)).
Qed.

Lemma has_beta_has_eta_preserves_abs
  {L L' : lambda_theory}
  {F : algebraic_theory_morphism L L'}
  (HL : has_β L)
  (HL' : has_η L')
  (Happ : ∏ n l, mor_app_ax F n l)
  (n : nat)
  (l : L (S n))
  : mor_abs_ax F n l.
Proof.
  refine (!HL' _ _ @ _).
  refine (maponpaths _ (!Happ _ _) @ _).
  exact (maponpaths (λ x, _ (_ x)) (HL _ _)).
Qed.
