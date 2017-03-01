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

Definition WellOrderedSet := ∑ X, isWellOrdered X.

Definition WellOrderedSet_to_OrderedSet (X:WellOrderedSet) : OrderedSet := pr1 X.

Coercion WellOrderedSet_to_OrderedSet : WellOrderedSet >-> OrderedSet.

Lemma isdeceq_wellOrderedSet (X:WellOrderedSet) : isdeceq X.
(* if this is true, then Zermelo's theorem needs [isdeceq X] as a hypothesis *)
Proof.
  intros x y.
  (* make the doubleton subset containing x and y *)
  set (S := λ z, ∥ (z=x) ⨿ (z=y) ∥).
  assert (x' := hinhpr (ii1 (idpath _)) : S x).
  assert (y' := hinhpr (ii2 (idpath _)) : S y).
  assert (h : ∃ s, S s).
  { apply hinhpr. exists x. exact x'. }
  assert (q := pr2 X S h); clear h.
  induction q as [s min], min as [h u].
  apply (squash_to_prop h).
  { apply isapropdec. (* uses funextemptyAxiom *) apply setproperty. }
  clear h. intro d. induction d as [d|d].
  - induction (!d); clear d.
    assert (v := u y y').
    (*
      v : x ≤ y
      ============================
      decidable (x = y)
     *)
    admit.
  - induction (!d); clear d.
    assert (v := u x x').
    (*
      v : y ≤ x
      ============================
      decidable (x = y)
     *)
    admit.
    (* it seems not to be true *)
Abort.
