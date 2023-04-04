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
      * exact (free_monoid (stnset n)).
      * apply isasetmonoid.
    + intros m n f g.
      exact (free_monoid_extend (λ i : stnset m, g i) f).
  - intros n i.
    exact (free_monoid_unit (i : stnset n)).
Defined.

Lemma free_monoid_is_clone : is_abstract_clone free_monoid_clone_data.
Proof.
  use make_is_abstract_clone.
  - intros m n i f.
    apply idpath.
  - intros n f.
    apply (free_monoid_extend_comp (idmonoidiso (free_monoid (stnset n)))).
  - intros l m n f_l f_m f_n.
    apply (maponpaths (λ x, pr1monoidfun _ _ x f_l)
      (@free_monoid_extend_funcomp2 (stnset l) _ _ f_m f_n)).
Qed.

Definition free_monoid_theory
  : algebraic_theory
  := algebraic_theory_weq_abstract_clone (make_abstract_clone _ free_monoid_is_clone).
