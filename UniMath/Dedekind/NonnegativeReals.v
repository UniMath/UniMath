(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Export UniMath.Foundations.Sets.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.DedekindCuts.

(*Local Open Scope Dcuts_scope.*)

(** ** Local definitions for non-negative real numbers *)

(** [hnnr_quot] is the set [DedekindCuts] quotientied by the equivalence relation [eqDedekindCuts] *)

Definition hnnr_quot : hSet := setquotinset eqDedekindCuts.

Definition Dcuts_to_hnnr_set : DedekindCuts -> hnnr_quot :=
  setquotpr eqDedekindCuts.


Lemma hnnr_quot_to_Dcuts_bounded :
  forall E : hnnr_quot, hexists (isUpperBound leDedekindCuts (pr1 E)).
Proof.
  destruct E as [E (x,(H,H0))] ; simpl.
  revert x.
  apply hinhfun.
  intros (x,Ex).
  exists x.
  intros y Hy.
  apply Dcuts_eq_le.
  now apply H0.
Qed.
Definition hnnr_quot_to_Dcuts : hnnr_quot -> DedekindCuts.
Proof.
  intros E.
  apply (lubDedekindCuts (pr1 E)).
  now apply hnnr_quot_to_Dcuts_bounded.
Defined.


(* Lemma hnnr_set_to_Dcuts_surj :
  forall x y : hnnr_set,
    Dcuts_eq (hnnr_set_to_Dcuts x) (hnnr_set_to_Dcuts y) -> x = y.
Proof.
  
Admitted.*)

Lemma hnnr_quot_to_Dcuts_bij :
  forall x : DedekindCuts, eqDedekindCuts (hnnr_quot_to_Dcuts (Dcuts_to_hnnr_set x)) x.
Proof.
  intros x.
  split.
  - apply islbub_Dcuts_lub.
    intros y Hy.
    now apply Dcuts_eq_ge.
  - apply isub_Dcuts_lub.
    now apply isrefl_Dcuts_eq.
Qed.
(*Lemma Dcuts_to_hnnr_set_bij :
  forall x : hnnr_set, (Dcuts_to_hnnr_set (hnnr_set_to_Dcuts x)) = x.
Proof.
Admitted.*)
  
(** Order *)

Local Definition hnnr_le : hrel hnnr_quot :=
  quotrel leDedekindCuts_comp.
Local Definition ispo_hnnr_le : isPartialOrder hnnr_le :=
  ispoquotrel leDedekindCuts_comp (pr2 (pr1 leDedekindCuts)).

Local Definition hnnr_ge : hrel hnnr_quot :=
  quotrel geDedekindCuts_comp.
Local Definition ispo_hnnr_ge : isPartialOrder hnnr_ge :=
  ispoquotrel geDedekindCuts_comp (pr2 geDedekindCuts).

Local Definition hnnr_lt : hrel hnnr_quot :=
  quotrel ltDedekindCuts_comp.
Local Definition isstpo_hnnr_lt : isStrictPartialOrder hnnr_lt :=
  isStrictPartialOrder_quotrel ltDedekindCuts_comp (pr2 ltDedekindCuts).

Local Definition hnnr_gt : hrel hnnr_quot :=
  quotrel gtDedekindCuts_comp.
Local Definition isstpo_hnnr_gt : isStrictPartialOrder hnnr_gt :=
  isStrictPartialOrder_quotrel gtDedekindCuts_comp (pr2 gtDedekindCuts).

(* (** Least Upper Bound *)

Definition hnnr_lub (E : hnnr_set -> hProp)
  (E_bounded : hexists (isub hnnr_le_rel E)) : hnnr_set.
Proof.
  set (F := fun x : Dcuts => E (Dcuts_to_hnnr_set x)).
  assert (F_bounded : hexists (isub Dcuts_le F)).
  { revert E_bounded.
    apply hinhfun.
    intros (ub,Hub).
    exists (hnnr_set_to_Dcuts ub).
    intros x Fx.
    assert (Ex : E (Dcuts_to_hnnr_set x)).
    admit.
    admit.
  }
  exists (Dcuts_eq (Dcuts_lub F F_bounded)).
  apply iseqclassconstr.
  intros P HP.
  apply HP.
  exists (Dcuts_lub F F_bounded).
  now apply isrefl_Dcuts_eq.
  intros.
  now apply istrans_Dcuts_eq with (1 := X0).
  intros.
  apply istrans_Dcuts_eq with (2 := X0).
  now apply issymm_Dcuts_eq.
Admitted.*)

(** * Export *)

Definition NonnegativeReals := hnnr_quot.

(** ** Order *)

Definition leNonnegativeReals : PartialOrder NonnegativeReals :=
  pairPartialOrder _ ispo_hnnr_le.
Definition geNonnegativeReals : PartialOrder NonnegativeReals :=
  pairPartialOrder _ ispo_hnnr_ge.
Definition ltNonnegativeReals : StrictPartialOrder NonnegativeReals :=
  pairStrictPartialOrder _ isstpo_hnnr_lt.
Definition gtNonnegativeReals : StrictPartialOrder NonnegativeReals :=
  pairStrictPartialOrder _ isstpo_hnnr_gt.

(** ** Opacify *)

Global Opaque NonnegativeReals.

(* End of the file hnnr.v *)

