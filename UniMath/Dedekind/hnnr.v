(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Import UniMath.Dedekind.Dcuts.

(*Local Open Scope Dcuts_scope.*)

(** ** Non-negative real numbers *)
(** Definition *)

Definition hnnr_set : hSet := setquotinset Dcuts_eq.

(* End of the file hnnr.v *)

