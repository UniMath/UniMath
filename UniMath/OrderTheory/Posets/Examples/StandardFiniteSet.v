(**************************************************************************************************

  The (partial) order on a standard finite set

  The standard finite set {0, ..., n - 1} inherits a (partial) order from the natural numbers.

  Contents
  1. The partially ordered set stn n [stnposet]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope stn.

(** * 1. The partially ordered set stn n *)

Definition stnposet ( n : nat ) : Poset.
Proof.
  unfold Poset.
  exists (_,,isasetstn n).
  unfold PartialOrder.
  exists (λ i j: ⟦n⟧, i ≤ j)%dnat.
  unfold isPartialOrder.
  split.
  - unfold ispreorder.
    split.
    * intros i j k. apply istransnatleh.
    * intros i. apply isreflnatleh.
  - intros i j r s. apply (invmaponpathsincl _ ( isinclstntonat _ )).
    apply isantisymmnatleh; assumption.
Defined.
