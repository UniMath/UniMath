(** * Univalent Basics.

Vladimir Voevodsky.
Feb. 2010 - Sep. 2011.


This file contains results which form a basis of the univalent
approach and which do not require the use of universes as
types. Fixpoints with values in a universe are used only once in the
definition [ isofhlevel ]. Many results in this file do not require
any axioms. The first axiom we use is [ funextempty ] which is the
functional extensionality axiom for functions with values in the empty
type. Closer to the end of the file we use general functional
extensionality [ funextfunax ] asserting that two homotopic functions
are equal. Since [ funextfunax ] itself is not an "axiom" in our sense
i.e. its type is not of h-level 1 we show that it is logically
equivalent to a real axiom [ funcontr ] which asserts that the space
of sections of a family with contractible fibers is contractible.

 *)

(* Port to coq trunk (8.4-8.5) in March 2014.  *)


(* The original file uu0 was split into the files uu0a, uu0b, uu0c and uu0d by
Vladimir Voevodsdy on Dec. 3, 2014. *)

Require Export uu0d.


(* End file *)