Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

(* Construct an algebraic theory as an abstract clone *)
Definition free_monoid_clone_data : abstract_clone_data.
Proof.
  use make_abstract_clone_data.
  - use make_algebraic_base.
    + intro n.
      use tpair.
      * exact (free_monoid (_ ,, isasetstn n)).
      * apply isasetmonoid.
    + intros m n f g.
      eapply free_monoid_universal_property; swap 1 2.
      * exact f.
      * exact g.
  - intros n i.
    apply (free_monoid_unit (i : pr1hSet (_ ,, isasetstn n))).
Defined.

Lemma free_monoid_is_clone : is_abstract_clone free_monoid_clone_data.
Proof.
  use make_is_abstract_clone.
  - intros m n i f.
    apply idpath.
  - intros n f.
    apply (free_monoid_extend_comp (idmonoidiso (free_monoid (_ ,, isasetstn n)))).
  - intros l m n f_l f_m f_n.
    simpl.
    revert f_l.
    apply list_ind.
    + apply idpath.
    + intros x xs IH.
      repeat rewrite map_cons.
      rewrite (iterop_list_mon_step (f_m _)).
      rewrite (iterop_list_mon_step (iterop_list_mon (map f_n _))).
      simpl.
      rewrite map_concatenate.
      rewrite (iterop_list_mon_concatenate (map f_n _)).
      simpl.
      apply maponpaths.
      exact IH.
Qed.

Definition free_monoid_theory
  : algebraic_theory
  := pr1weq
    algebraic_theory_weq_abstract_clone
    (make_abstract_clone _ free_monoid_is_clone).
