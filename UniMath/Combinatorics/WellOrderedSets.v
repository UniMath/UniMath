(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.
Local Open Scope poset.

Definition isWellOrdered (X:OrderedSet) : hProp.
Proof.
  (* first define the property *)
  exists (∏ S : hsubtype X, (∃ s, S s) -> ∑ s:X, S s × ∏ t:X, S t -> s ≤ t).
  (* now prove it's a propostion *)
  apply impred; intro S; apply impred; intro s; clear s. apply invproofirrelevance; intros s t.
  apply subtypeEquality.
  * intros x. apply isapropdirprod.
    + apply propproperty.
    + apply impred; intro y. apply impred; intros _. apply propproperty.
  * induction s as [x i], t as [y j], i as [I i], j as [J j]; simpl.
    apply (squash_to_prop (OrderedSet_istotal x y)).
    { apply setproperty. }
    intro c. induction c as [xley|ylex].
    - apply OrderedSet_isantisymm.
      + assumption.
      + now apply j.
    - apply OrderedSet_isantisymm.
      + now apply i.
      + assumption.
Defined.
