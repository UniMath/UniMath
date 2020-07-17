(** * Signatures for universal algebra *)

(**
This file contains a formalization of single-sorted signatures defined as a vector of arities.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.Universal.MoreLists.

Local Open Scope stn.

Definition signature: UU := ∑ S O: UU, O → list S × S.

Definition sorts (Σ: signature) := pr1 Σ.

Definition opsyms (Σ: signature) := pr12 Σ.

Coercion opsyms : signature >-> UU.

Definition ar (Σ: signature) := pr22 Σ.

Definition arity {Σ: signature} (σ: Σ) : list (sorts Σ) := pr1 (ar Σ σ).

Definition sort {Σ: signature} (σ: Σ) : sorts Σ := pr2 (ar Σ σ).

Definition make_signature (S: UU) (O: UU) (ar: O → list S × S) : signature := S ,, (O ,, ar).

Definition make_signature_single_sorted (O: UU) (ar: O → nat) : signature
  := make_signature unit O (λ op, (list_fill tt (ar op)) ,, tt).

(** ** Some additional types to simplify the definition of signatures *)

Definition signature_simple : UU := ∑ (ns: nat), list (list (⟦ ns ⟧) × ⟦ ns ⟧).

Definition make_signature_simple {ns: nat} (ar: list (list (⟦ ns ⟧) × ⟦ ns ⟧))
  : signature_simple := ns ,, ar.

Coercion signature_simple_compile (Σ: signature_simple) : signature
  := make_signature (⟦ pr1 Σ ⟧) (⟦ length (pr2 Σ) ⟧) (nth (pr2 Σ)).

Definition signature_simple_single_sorted : UU := list nat.

Definition make_signature_simple_single_sorted (ar: list nat) : signature_simple_single_sorted := ar.

Coercion signature_simple_single_sorted_compile (Σ: signature_simple_single_sorted): signature
  := make_signature_single_sorted (⟦ length Σ ⟧) (nth Σ).
