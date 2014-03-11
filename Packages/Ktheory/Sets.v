(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.hSet.
Require Ktheory.Utilities.
Import Utilities.Notation.
Definition unit : hSet := tpair isaset unit isasetunit.
Definition Product {I} (X:I -> hSet) : hSet.
  intros. exists (Utilities.sections (funcomp X set_to_type)).
  apply (impred 2); intros i. apply (pr2 (X i)). Defined.    
