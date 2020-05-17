(** * Signatures for universal algebra *)

(**
This file contains a formalization of single-sorted signatures defined as a vector of arities.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Definition Arity: UU := nat.

Definition signature: UU := ∑ (names: hSet), names → Arity.

Definition make_signature (names: hSet) (aritymap: names → Arity): signature
    := names ,, aritymap.

Definition make_signature_simple {n: nat} (v: Vector nat n): signature
    := make_signature (stnset n) (el v).

Definition names (sigma: signature): hSet := pr1 sigma.

Definition arity {sigma: signature} (nm: names sigma): Arity := pr2 sigma nm.
