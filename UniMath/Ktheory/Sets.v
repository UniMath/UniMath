(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities.
Definition unit : hSet := ((unit:UU),,isasetunit).
Definition Product {I} (X:I -> hSet) : hSet.
  intros. exists (Utilities.Section (funcomp X set_to_type)).
  apply (impred 2); intros i. apply (pr2 (X i)). Defined.    
