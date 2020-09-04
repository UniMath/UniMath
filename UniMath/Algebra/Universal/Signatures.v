(** * Signatures for universal algebra *)

(**
This file contains a formalization of multi-sorted signatures defined as a vector of arities.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Export UniMath.Algebra.Universal.DecSet.
Require Import UniMath.Algebra.Universal.MoreLists.

Local Open Scope stn.

Definition signature : UU := ∑ (S: decSet) (O: hSet), O → list S × S.

Definition sorts (σ: signature) := pr1 σ.

Definition names (σ: signature) := pr12 σ.

Definition ar (σ: signature) := pr22 σ.

Definition arity {σ: signature} (nm: names σ) : list (sorts σ) := pr1 (ar σ nm).

Definition sort {σ: signature} (nm: names σ) : sorts σ := pr2 (ar σ nm).

Definition make_signature (S: decSet) (O: hSet) (ar: O → list S × S) : signature 
  := S ,, (O ,, ar).

Definition make_signature_single_sorted (O: hSet) (ar: O → nat) : signature
  := make_signature (unit,, isdecequnit) O (λ op, fill tt (ar op) ,, tt).

(** ** Some additional types to simplify the definition of signatures *)

Definition signature_simple : UU := ∑ (ns: nat), list (list (⟦ ns ⟧) × ⟦ ns ⟧).

Definition make_signature_simple {ns: nat} (ar: list (list (⟦ ns ⟧) × ⟦ ns ⟧))
  : signature_simple := ns ,, ar.

Coercion signature_simple_compile (σ: signature_simple) : signature
  := make_signature (⟦ pr1 σ ⟧ ,, isdeceqstn _) (stnset (length (pr2 σ))) (nth (pr2 σ)).

Definition signature_simple_single_sorted : UU := list nat.

Definition make_signature_simple_single_sorted (ar: list nat) : signature_simple_single_sorted := ar.

Coercion signature_simple_single_sorted_compile (σ: signature_simple_single_sorted): signature
  := make_signature_single_sorted (stnset (length σ)) (nth σ).
