(**************************************************************************************************

  Scott's original representation theorem

  In 1980, Dana Scott showed that a every λ-theory L arises as the endomorphism of λ x, x in the
  category of retracts of L. This file gives a partial proof of this. It gives the functions between
  L and the endomorphism theory, and shows that they give a bijection on L_0.

  Contents
  1. The endomorphism theory [E]
  2. The partial isomorphism [representation_theorem_iso_0]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.Combinators.

Require Import Ltac2.Ltac2.

Local Open Scope algebraic_theories.
Local Open Scope lambda_calculus.

(** * 1. The endomorphism theory *)

Section RepresentationTheorem.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Definition E
    : lambda_theory.
  Proof.
    refine '(endomorphism_lambda_theory _ _ _ _ _ _).
    - exact (R (n := 0) L Lβ).
    - exact (R_terminal _ _ (c := abs (var (stnweq (inr tt))))).
    - apply R_binproducts.
    - exact (U L Lβ).
    - apply R_exponentials.
    - apply R_section.
    - apply R_retraction.
  Defined.

  Definition Eβ
    : has_β E.
  Proof.
    apply endomorphism_theory_has_β.
    apply R_retraction_is_retraction.
  Qed.

(** * 2. The partial isomorphism *)

  Definition representation_theorem_iso_mor_0
    : E 0 → L 0.
  Proof.
    intro f.
    exact (app (R_mor_to_L L f) (U_term L)).
  Defined.

  Definition representation_theorem_iso_inv_0
    : L 0 → E 0.
  Proof.
    intro f.
    exists (abs (inflate f)).
    abstract (now (
      refine '(maponpaths (λ x, x ∘ _) ((U_compose _ Lβ _)) @ _);
      refine '(compose_abs _ Lβ _ _ @ _);
      refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _);
      refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _);
      refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _);
      refine '(maponpaths (λ x, (abs x)) (subst_inflate _ _ _) @ _);
      now do 2 (refine '(maponpaths (λ x, abs (_ • x)) (pr2 (iscontr_empty_tuple (L 1)) _) @ !_))
    )).
  Defined.

  Definition representation_theorem_iso_mor
    {n : nat}
    : E n → L n.
  Proof.
    induction n as [ | n Fn ].
    - exact representation_theorem_iso_mor_0.
    - intro f.
      exact (app
        (inflate (Fn (abs f)))
        (var (stnweq (inr tt)))).
  Defined.

  Definition representation_theorem_iso_inv
    {n : nat}
    : L n → E n.
  Proof.
    induction n as [ | n Fn ].
    - exact representation_theorem_iso_inv_0.
    - intro f.
      exact (app
        (inflate (Fn (abs f)))
        (var (T := E) (stnweq (inr tt)))).
  Defined.

  Lemma representation_theorem_iso_inv_mor_0
    (f : E 0)
    : representation_theorem_iso_inv (representation_theorem_iso_mor f) = f.
  Proof.
    apply R_mor_eq.
    refine '(maponpaths (λ x, (abs x)) (inflate_app _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _) @ _).
    refine '(_ @ R_mor_is_mor_right _ Lβ _).
    refine '(_ @ !compose_abs _ Lβ _ _).
    refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _)).
    refine '(_ @ !maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _)).
    exact (!maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _)).
  Qed.

  Lemma representation_theorem_iso_mor_inv_0
    (f : L 0)
    : representation_theorem_iso_mor (representation_theorem_iso_inv f) = f.
  Proof.
    refine '(beta_equality _ Lβ _ _ @ _).
    refine '(subst_inflate _ _ _ @ _).
    refine '(_ @ subst_var L f).
    now do 2 (refine '(maponpaths (λ x, _ • x) (pr2 (iscontr_empty_tuple _) _) @ !_)).
  Qed.

  Lemma representation_theorem_is_iso_0
    : is_inverse_in_precat (C := HSET%cat) representation_theorem_iso_mor_0 representation_theorem_iso_inv_0.
  Proof.
    split;
      apply funextfun;
      intro f.
    - apply R_mor_eq.
      refine '(maponpaths (λ x, (abs x)) (inflate_app _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _) @ _).
      refine '(_ @ R_mor_is_mor_right L Lβ _).
      refine '(_ @ !compose_abs _ Lβ _ _).
      refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _)).
      refine '(_ @ !maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _)).
      exact (!maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _)).
    - refine '(beta_equality _ Lβ _ _ @ _).
      refine '(subst_inflate _ _ _ @ _).
      refine '(_ @ subst_var L f).
      now do 2 (refine '(maponpaths (λ x, _ • x) (pr2 (iscontr_empty_tuple _) _) @ !_)).
  Qed.

  Definition representation_theorem_iso_0
    : z_iso (C := HSET%cat) (E 0) (L 0)
    := make_z_iso (C := HSET%cat)
      representation_theorem_iso_mor_0
      representation_theorem_iso_inv_0
      representation_theorem_is_iso_0.

End RepresentationTheorem.
