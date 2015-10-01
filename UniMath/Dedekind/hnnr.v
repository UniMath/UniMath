(** * Definition of non-negative real numbers using Dedekind cuts *)
(** Catherine Lelay. Sep. 2015 *)

Require Export UniMath.Foundations.Sets.
Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Dcuts.

(*Local Open Scope Dcuts_scope.*)

(** ** Non-negative real numbers *)
(** Definition *)

Definition hnnr_set : hSet := setquotinset Dcuts_eq.

Definition Dcuts_to_hnnr_set : Dcuts -> hnnr_set :=
  setquotpr Dcuts_eq.


Lemma hnnr_set_to_Dcuts_bounded :
  forall E : hnnr_set, hexists (isub Dcuts_le (pr1 E)).
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
Definition hnnr_set_to_Dcuts : hnnr_set -> Dcuts.
Proof.
  intros E.
  apply (Dcuts_lub (pr1 E)).
  now apply hnnr_set_to_Dcuts_bounded.
Defined.


(* Lemma hnnr_set_to_Dcuts_surj :
  forall x y : hnnr_set,
    Dcuts_eq (hnnr_set_to_Dcuts x) (hnnr_set_to_Dcuts y) -> x = y.
Proof.
  
Admitted.*)

Lemma hnnr_set_to_Dcuts_bij :
  forall x : Dcuts, Dcuts_eq (hnnr_set_to_Dcuts (Dcuts_to_hnnr_set x)) x.
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

Local Definition hnnr_le_rel : hrel hnnr_set := quotrel Dcuts_le_comp.
Local Definition ispo_hnnr_le_rel : ispo (hnnr_le_rel) := ispoquotrel Dcuts_le_comp ispo_Dcuts_le.
Definition hnnr_le : po hnnr_set :=
  popair _ ispo_hnnr_le_rel.

Local Definition hnnr_ge_rel : hrel hnnr_set := quotrel Dcuts_ge_comp.
Local Definition ispo_hnnr_ge_rel : ispo (hnnr_ge_rel) := ispoquotrel Dcuts_ge_comp ispo_Dcuts_ge.
Definition hnnr_ge : po hnnr_set :=
  popair _ ispo_hnnr_ge_rel.

Local Definition hnnr_lt_rel : hrel hnnr_set := quotrel Dcuts_lt_comp.
Local Definition hnnr_gt_rel : hrel hnnr_set := quotrel Dcuts_gt_comp.

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

Notation hnnr := hnnr_set.

(* End of the file hnnr.v *)

