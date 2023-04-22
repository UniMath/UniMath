Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
(* Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras. *)

Local Open Scope vec_scope.

Definition one_point_theory
  : algebraic_theory.
Proof.
  use make_algebraic_theory'.
  - exact (λ _, (unit ,, isasetunit)).
  - exact (λ _ _, tt).
  - exact (λ _ _ _ _, tt).
  - abstract (
      intros m n i f;
      now induction (f i)
    ).
  - abstract (
      intros n f;
      now induction f
    ).
  - abstract now do 6 intro.
Defined.

Lemma one_point_clone_algebra_is_trivial
  : ∏ (A : abstract_clone_algebra one_point_clone), A ≃ unit.
Proof.
  intro A.
  apply weqcontrtounit.
  use tpair.
  - use (action (tt : one_point_clone 0) (weqvecfun 0 vnil)).
  - intro a.
    rewrite <- (abstract_clone_algebra_action_projects_component _ _ (make_stn 1 0 (idpath _)) (λ _, a) : _ = a).
    exact (lift_constant_action _ _ _).
Qed.
