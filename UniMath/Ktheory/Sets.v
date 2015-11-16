(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.

(* move upstream: *)
Definition unit : hSet := ((unit:UU),,isasetunit).
Definition Product {I} (X:I -> hSet) : hSet.
  intros. exists (Section X). apply impred_isaset; intros i. apply setproperty. Defined.
