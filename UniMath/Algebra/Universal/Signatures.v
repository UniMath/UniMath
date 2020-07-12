(** * Signatures for universal algebra *)

(**
This file contains a formalization of single-sorted signatures defined as a vector of arities.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.Universal.MoreLists.

Open Scope stn.

Definition signature: UU := ∑ S O: UU, O → list S × S.

Definition sorts (Σ: signature) := pr1 Σ.

Definition opsyms (Σ: signature) := pr12 Σ.

Coercion opsyms : signature >-> UU.

Definition ar (Σ: signature) := pr22 Σ.

Definition arity {Σ: signature} (σ: Σ) : list (sorts Σ) := pr1 (ar Σ σ).

Definition sort {Σ: signature} (σ: Σ) : sorts Σ := pr2 (ar Σ σ).

Definition make_signature (S: UU) (O: UU) (ar: O → list S × S) : signature := S ,, (O ,, ar).

Definition make_single_sorted_signature (O: UU) (ar: O → nat) : signature
  := make_signature unit O (λ op, (list_fill tt (ar op)) ,, tt).

Definition make_signature_simple_single_sorted (ar: list nat) : signature
  := make_single_sorted_signature  (⟦ length ar ⟧) (nth ar).

Definition make_signature_simple (n: nat) (ar: list (list (stn n) × stn n)) : signature
  := make_signature (⟦ n ⟧) (⟦ length ar ⟧) (nth ar).
