(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Export UniMath.Foundations.Sets.
Require Import UniMath.Dedekind.Dcuts.

(*Local Open Scope Dcuts_scope.*)

(** ** Non-negative real numbers *)
(** Definition *)

Definition hnnr_set : hSet := setquotinset Dcuts_eq.

(** Order *)

Definition hnnr_le_rel : hrel hnnr_set.
Proof.
  apply (quotrel (L := Dcuts_le)).
  exact Dcuts_le_comp.
Defined.


(** * Notations *)

Notation hnnr := hnnr_set.

(* End of the file hnnr.v *)

