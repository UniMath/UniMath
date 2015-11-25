(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Unset Automatic Introduction.

(* move upstream: *)
Definition unit : hSet := ((unit:UU),,isasetunit).

Definition Product {I} (X:I -> hSet) : hSet
  := (∀ i, X i) % set.
