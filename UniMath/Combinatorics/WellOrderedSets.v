(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.
Local Open Scope poset.

Definition isClosedSubposet {W:Poset} (Y X:hsubtype W) : hProp.
Proof.
  exists (
      (∏ x:W, Y x -> X x)
        ×
        (∏ (x y:W), Y y -> X x -> x ≤ y -> Y x)).
  apply isapropdirprod.
  - apply impred; intro y; apply impred; intro h. apply propproperty.
  - apply impred; intro x; apply impred; intro y; apply impred; intro k;
      apply impred; intro h; apply impred; intro le.
    apply propproperty.
Defined.

Definition WellOrderedSet := ∑ (X:hSet) (R:hrel X), isWellOrder R.

Definition WellOrderedSet_to_OrderedSet (X:WellOrderedSet) : OrderedSet.
Proof.
  unfold WellOrderedSet in X.
  unfold isWellOrder in X.
  unfold isTotalOrder in X.
  use tpair.
  - use tpair.
    + exact (pr1 X).
    + simpl. use tpair.
      * exact (pr1 (pr2 X)).
      * simpl. exact (pr1 (pr1 (pr2 (pr2 X)))).
  - simpl. exact (pr2 (pr1 (pr2 (pr2 X)))).
Defined.

Coercion WellOrderedSet_to_OrderedSet : WellOrderedSet >-> OrderedSet.

Definition SubsetWithWellOrdering (X:hSet) :=
  ∑ (S:hsubtype X) (R : hrel S), isWellOrder R.

Definition SubsetWithWellOrdering_to_subtype {X:hSet} : SubsetWithWellOrdering X -> hsubtype X
  := pr1.

Coercion SubsetWithWellOrdering_to_subtype : SubsetWithWellOrdering >-> hsubtype.

Local Definition rel {X:hSet} (S : SubsetWithWellOrdering X) : hrel S
  := pr1 (pr2 S).

Local Notation " s ≤ s' " := (rel _ s s').

Definition isIn {X:UU} {S:hsubtype X} (s:S) (T:hsubtype X) := T (pr1 s).

Local Notation " s ∈ T " := (isIn s T) (at level 45).

Definition smallerSubtype {X:UU} (S T : hsubtype X) : hProp.
Proof.
  exists (∏ s:S, s ∈ T). apply impred; intros x. apply propproperty.
Defined.

Local Notation " S ⊆ T " := (smallerSubtype S T) (at level 45).

Local Definition inc {X:UU} {S T : hsubtype X} : S ⊆ T -> S -> T.
Proof.
  intros le s. exact (pr1 s,, le s).
Defined.

Local Definition subposet {X:hSet} {S T:SubsetWithWellOrdering X} (le : S ⊆ T) : hProp.
Proof.
  exists (∏ s s' : S, s ≤ s' <-> inc le s ≤ inc le s').
  apply impred; intro. apply impred; intro. apply isapropdirprod.
  - apply impred; intros _. apply propproperty.
  - apply impred; intros _. apply propproperty.
Defined.

Local Definition isclosed {X:hSet} {S:hsubtype X} {T:SubsetWithWellOrdering X} (le : S ⊆ T) : hProp.
Proof.
  exists (∏ (s:S) (t:T), t ≤ inc le s -> pr1 t ∈ S).
  apply impred; intro. apply impred; intro. apply impred; intros _. apply propproperty.
Defined.

Definition isClosed {X:hSet} (S T:SubsetWithWellOrdering X) : hProp
  (* condition:
     S should be a subset of T
     the ordering on S should be induced by the ordering on T
     S should be a closed subset of T, i.e., an initial portion
   *)
  := (∑ (le : S ⊆ T), subposet le ∧ isclosed le)%prop.

