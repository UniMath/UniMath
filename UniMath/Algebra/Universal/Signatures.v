(** * Signatures for universal algebra. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(*
This file contains a formalization of multi-sorted signatures.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Export UniMath.Combinatorics.DecSet.
Require Import UniMath.Combinatorics.MoreLists.

Local Open Scope stn.

(** A _signature_ is given by a decidable set of sorts, a set of of operation symbols and a map
from operation symbols to pair [(l,, s)] where [l] is the _arity_ (or _domain_) and [s] is
the _sort_ (or _range_).
*)

Definition signature : UU := ∑ (S: decSet) (O: hSet), O → list S × S.

Definition sorts (σ: signature) := pr1 σ.

Definition names (σ: signature) := pr12 σ.

Definition ar (σ: signature) := pr22 σ.

Definition arity {σ: signature} (nm: names σ) : list (sorts σ) := pr1 (ar σ nm).

Definition sort {σ: signature} (nm: names σ) : sorts σ := pr2 (ar σ nm).

(** Helper function for creating signatures. *)

Definition make_signature (S: decSet) (O: hSet) (ar: O → list S × S) : signature
  := S ,, (O ,, ar).

Definition make_signature_single_sorted (O: hSet) (ar: O → nat) : signature
  := make_signature (unit,, isdecequnit) O (λ op, fill tt (ar op) ,, tt).

(** A signature may be alternatively specified trough a [signature_simple]. In a simple
signature, the types for sorts and operation symbols are standard finite sets, and
the map from operations symbols to domain and range is replaced by a list. In this way,
the definition of a new signature is made simpler.

We have decided to define new types for simple signatures instead of only defining helper
functions, since this make it simpler to define simplified means of defining a new algebra,
too.
 *)

Definition signature_simple : UU := ∑ (ns: nat), list (list (⟦ ns ⟧) × ⟦ ns ⟧).

Definition make_signature_simple {ns: nat} (ar: list (list (⟦ ns ⟧) × ⟦ ns ⟧))
  : signature_simple := ns ,, ar.

Coercion signature_simple_compile (σ: signature_simple) : signature
  := make_signature (⟦ pr1 σ ⟧ ,, isdeceqstn _) (stnset (length (pr2 σ))) (nth (pr2 σ)).

Definition signature_simple_single_sorted : UU := list nat.

Definition make_signature_simple_single_sorted (ar: list nat) : signature_simple_single_sorted := ar.

Coercion signature_simple_single_sorted_compile (σ: signature_simple_single_sorted): signature
  := make_signature_single_sorted (stnset (length σ)) (nth σ).
