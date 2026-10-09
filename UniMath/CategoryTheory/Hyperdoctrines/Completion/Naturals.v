(**

 Natural numbers in the completion of a hyperdoctrine

 In a preorder tripos, we have a preorder of formulas in every context. However,
 in practice it is easier to work with a partial order since various laws of
 formulas then hold up to equality rather than up to isomorphism. We already
 showed that every preorder tripos can be completed to a weak tripos. Here we
 extend this result to include natural numbers.

 Recall that a natural numbers type in a first-order hyperdoctrine consists of
 - a type `N`
 - a term `z : N`
 - a term `s : N → N`
 such that we can prove in the first-order hyperdoctrine that `s` is injective
 and that `z` isn't the successor of any number.

 If we take the completion of a first-order hyperdoctrine, then the category of
 types and terms stays the same: we only change the formulas since we quotient
 them by isomorphism. For this reason, we can almost directly show that the
 completion comes with natural numbers. The work lies in showing that the required
 axioms still hold in the completion. These axioms can also be proved in a rather
 direct manner, because the functor from a preorder hyperdoctrine to its completion
 preserves all connectives in first-order logic.

 Content
 1. The data
 2. The laws
 3. The natural numbers

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.HyperdoctrineNat.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Completion.WeakEquivs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Completion.Construction.

Section Naturals.
  Context {H : first_order_preorder_hyperdoctrine}
          (N : first_order_preorder_hyperdoctrine_nats H).

  Let Hc : first_order_hyperdoctrine
    := first_order_preorder_hyperdoctrine_completion H.

  (** * 1. The data *)
  Definition first_order_preorder_hyperdoctrine_completion_nats_data
    : first_order_hyperdoctrine_nats_data Hc.
  Proof.
    use make_first_order_hyperdoctrine_nats_data.
    - exact N.
    - exact (pr121 N).
    - exact (pr221 N).
  Defined.

  (** * 2. The laws *)
  Proposition first_order_preorder_hyperdoctrine_completion_nats_axioms
    : first_order_hyperdoctrine_nats_axioms
        first_order_preorder_hyperdoctrine_completion_nats_data.
  Proof.
    split.
    - unfold first_order_hyperdoctrine_nats_zs_axiom.
      pose (to_completion_proof H (pr12 N)) as p.
      rewrite to_completion_truth in p.
      rewrite to_completion_forall in p.
      rewrite to_completion_impl in p.
      rewrite to_completion_false in p.
      rewrite to_completion_equal in p.
      exact p.
    - unfold first_order_hyperdoctrine_nats_zs_axiom.
      pose (to_completion_proof H (pr22 N)) as p.
      rewrite to_completion_truth in p.
      rewrite !to_completion_forall in p.
      rewrite !to_completion_impl in p.
      rewrite !to_completion_equal in p.
      exact p.
  Qed.

  (** * 3. The natural numbers *)
  Definition first_order_preorder_hyperdoctrine_completion_nats
    : first_order_hyperdoctrine_nats Hc.
  Proof.
    use make_first_order_hyperdoctrine_nats.
    - exact first_order_preorder_hyperdoctrine_completion_nats_data.
    - exact first_order_preorder_hyperdoctrine_completion_nats_axioms.
  Defined.
End Naturals.
