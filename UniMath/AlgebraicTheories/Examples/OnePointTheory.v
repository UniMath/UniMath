Require Import UniMath.Foundations.All.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

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
    induction (f i).
    apply idpath.
  - intros n f.
    induction f.
    apply idpath.
  - intros l m n f_l f_m f_n.
    apply idpath.
Qed.

Definition one_point_theory
  : algebraic_theory
  := algebraic_theory_weq_abstract_clone (make_abstract_clone _ one_point_is_clone).
