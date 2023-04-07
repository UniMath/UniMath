Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneAlgebras.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

Local Open Scope multmonoid_scope.
Local Open Scope algebraic_theory.
Local Open Scope vec_scope.

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
  - now do 4 intro.
  - intros n f.
    apply (free_monoid_extend_comp (idmonoidiso (free_monoid (stnset n)))).
  - intros l m n f_l f_m f_n.
    apply (maponpaths (λ x, pr1monoidfun _ _ x f_l)
      (@free_monoid_extend_funcomp2 (stnset l) _ _ f_m f_n)).
Qed.

Definition free_monoid_clone
  : abstract_clone
  := make_abstract_clone _ free_monoid_is_clone.

Definition free_monoid_theory
  : algebraic_theory
  := algebraic_theory_weq_abstract_clone free_monoid_clone.

Definition setwithbinop_from_free_monoid_algebra (A : abstract_clone_algebra free_monoid_clone)
  : setwithbinop.
Proof.
  use make_setwithbinop.
  - exact A.
  - intros a b.
    eapply action.
    + exact (op
      (free_monoid_unit (make_stn 2 0 (idpath _) : stnset _))
      (free_monoid_unit (make_stn 2 1 (idpath _) : stnset _))).
    + exact (weqvecfun _ [(a ; b)]).
Defined.

Definition empty_list {X : UU} : (stn 0 → X) := (λ i, (fromempty (negnatlthn0 _ (stnlt i)))).

Definition free_monoid_algebra_unit (A : abstract_clone_algebra free_monoid_clone)
  : setwithbinop_from_free_monoid_algebra A
  := (@action free_monoid_clone _ 0 1 empty_list).

Definition lift_constant {C : abstract_clone_data} (n : nat) (f : C 0) : C n := f • empty_list.

Lemma transport_constants
  {A : abstract_clone_algebra free_monoid_clone}
  (n : nat)
  (f : free_monoid_clone 0)
  (a : stn n → A)
  : action f empty_list = action (lift_constant n f) a.
Proof.
  unfold lift_constant.
  rewrite abstract_clone_algebra_action_is_assoc.
  apply maponpaths, funextfun.
  intro i.
  exact (fromempty (negnatlthn0 _ (stnlt i))).
Qed.

Lemma move_action_through_weqvecfun {A : abstract_clone_algebra free_monoid_clone} {n f g} (h : stn n → A)
  : weqvecfun _ [( action f h ; action g h )] = λ i, action (weqvecfun _  [(f ; g)] i) h.
Proof.
  now apply (invmaponpathsweq (invweq (weqvecfun _))).
Qed.

Lemma free_monoid_algebra_op_is_assoc (A : abstract_clone_algebra free_monoid_clone)
  : isassoc (@op (setwithbinop_from_free_monoid_algebra A)).
Proof.
  intros a b c.
  unfold op, setwithbinop_from_free_monoid_algebra, make_setwithbinop.
  pose (f := weqvecfun _ [(a ; b ; c)]).
  pose (Hf := λ i Hi,
    !(abstract_clone_algebra_action_projects_component _ _ (make_stn 3 i Hi) f)).
  rewrite pr2_of_pair,
    (Hf 0 (idpath true) : a = _),
    (Hf 1%nat (idpath true) : b = _),
    (Hf 2 (idpath true) : c = _).
  now do 4 (rewrite move_action_through_weqvecfun, <- abstract_clone_algebra_action_is_assoc).
Qed.

Lemma free_monoid_algebra_op_is_unital (A : abstract_clone_algebra free_monoid_clone) 
  : isunital (@op (setwithbinop_from_free_monoid_algebra A)).
Proof.
  use (free_monoid_algebra_unit A ,, (_ ,, _));
    unfold islunit, isrunit;
    intro;
    unfold free_monoid_algebra_unit, op, setwithbinop_from_free_monoid_algebra, make_setwithbinop;
    now rewrite pr2_of_pair,
      <- (abstract_clone_algebra_action_projects_component _ _ (make_stn 1 0 (idpath true)) (λ _, x)),
      (transport_constants 1 _ (λ _, x)),
      move_action_through_weqvecfun,
      <- abstract_clone_algebra_action_is_assoc.
Qed.

Lemma free_monoid_algebra_op_is_monoidop (A : abstract_clone_algebra free_monoid_clone)
  : ismonoidop (@op (setwithbinop_from_free_monoid_algebra A)).
Proof.
  exact (free_monoid_algebra_op_is_assoc A ,, free_monoid_algebra_op_is_unital A).
Qed.