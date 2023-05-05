Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

Local Open Scope vec_scope.

(* Construct an algebraic theory as an abstract clone *)
Definition one_point_clone_data
  : abstract_clone_data
  := make_abstract_clone_data
    (make_algebraic_base
      (λ _, (unit ,, isasetunit))
      (λ _ _ _ _, tt))
    (λ _ _, tt).

Lemma one_point_is_clone : is_abstract_clone one_point_clone_data.
Proof.
  use make_is_abstract_clone.
  - intros m n i f.
    now induction (f i).
  - intros n f.
    now induction f.
  - now do 6 intro.
Qed.

Definition one_point_clone
  : abstract_clone
  := make_abstract_clone _ one_point_is_clone.

Definition one_point_theory
  : algebraic_theory
  := algebraic_theory_weq_abstract_clone one_point_clone.

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
