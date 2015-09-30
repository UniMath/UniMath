(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Export UniMath.Foundations.Sets.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Dcuts.

(*Local Open Scope Dcuts_scope.*)

(** ** Non-negative real numbers *)
(** Definition *)

Definition hnnr_set : hSet := setquotinset Dcuts_eq.

(** Order *)

Definition hnnr_le_rel : hrel hnnr_set := quotrel Dcuts_le_comp.
Definition hnnr_lt_rel : hrel hnnr_set := quotrel Dcuts_lt_comp.
Definition hnnr_ge_rel : hrel hnnr_set := quotrel Dcuts_ge_comp.
Definition hnnr_gt_rel : hrel hnnr_set := quotrel Dcuts_gt_comp.

(** Least Upper Bound *)

Definition hnnr_lub (E : hnnr_set -> hProp)
  (E_bounded : hexists (isub hnnr_le_rel E)) : hnnr_set.
Proof.
  set (F := fun x : Dcuts => hexists (fun X : hnnr_set => dirprod (E X) (pr1 X x))).
  assert (F_bounded : hexists (isub Dcuts_le F)).
    apply E_bounded ; intros ((UB,(ub,(Hub1,Hub2))),HUB).
    revert ub HUB. ; apply hinhfun2 ; intros (ub,Hub).

  exists (Dcuts_eq (Dcuts_lub F F_bounded)).
  apply iseqclassconstr.
  Search ishinh.
  intros P HP.
  apply HP.
  exists (Dcuts_lub F F_bounded).
  now apply isrefl_Dcuts_eq.
Admitted.

(** * Notations *)

Notation hnnr := hnnr_set.

(* End of the file hnnr.v *)

