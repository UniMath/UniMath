Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

(* Construct an algebraic theory as an abstract clone *)
Definition one_point_clone_data : abstract_clone_data.
Proof.
  use make_abstract_clone_data.
  - use make_algebraic_base.
    + intro.
      exact (unit ,, isasetunit).
    + intros.
      exact tt.
  - intros.
    exact tt.
Defined.

Definition one_point_is_clone : is_abstract_clone one_point_clone_data.
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

Definition one_point_theory : algebraic_theory.
Proof.
  apply (pr1weq algebraic_theory_weq_abstract_clone).
  exact (make_abstract_clone one_point_clone_data one_point_is_clone).
Defined.