(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Fields_comp.
Require Import UniMath.Dedekind.Complements.


Opaque hq.

Open Scope hq_scope.

(** ** Definition of non-negative rational numbers *)

Local Definition hnnq_def := carrier (hqleh 0).

Local Definition hnnq_def_to_hq (r : hnnq_def) : hq := pr1 r.
Coercion hnnq_def_to_hq : hnnq_def >-> pr1hSet.
Local Definition hq_to_hnnq_def (r : hq) (Hr : hqleh 0 r) : hnnq_def :=
  tpair (fun x : hq => hqleh 0 x) r Hr.

Lemma isincl_hnnq_to_hq : isincl hnnq_def_to_hq. 
Proof. 
  apply (isinclpr1 (fun x : hq => hqleh 0 x) (fun x : hq => isapropneg (hqgth 0 x))).
Qed.
Local Definition hnnq_set : hSet := 
  hSetpair _ (isasetsubset hnnq_def_to_hq isasethq isincl_hnnq_to_hq).

(** ** Equality and order on non-negative rational numbers *)

(** *** Order *)

Local Definition hnnq_le : hrel hnnq_def := resrel hqleh (hqleh 0).
Lemma isPartialOrder_hnnq_le : ispo hnnq_le.
Proof.
  split.
  intros x y z.
  now apply istranshqleh.
  intros x.
  now apply isreflhqleh.
Qed.  
  
Local Definition hnnq_ge : hrel hnnq_def := resrel hqgeh (hqleh 0).
Lemma isPartialOrder_hnnq_ge : ispo hnnq_ge.
Proof.
  destruct isPartialOrder_hnnq_le as [Htrans Hrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hrefl.
Qed.

Local Definition hnnq_lt : hrel hnnq_def := resrel hqlth (hqleh 0).
Lemma isStrictPartialOrder_hnnq_lt : isStrictPartialOrder hnnq_lt.
Proof.
  split.
  intros x y z.
  now apply istranshqlth.
  intros x.
  now apply isirreflhqlth.
Qed.

Local Definition hnnq_gt : hrel hnnq_def := resrel hqgth (hqleh 0).
Lemma isStrictPartialOrder_hnnq_gt : isStrictPartialOrder hnnq_gt.
Proof.
  destruct isStrictPartialOrder_hnnq_lt as [Htrans Hirrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hirrefl.
Qed.

(** ** Non-negative rational numbers are a commutative rig *)

Local Definition hnnq_plus_submonoid : issubmonoid (X := fld_to_addmonoid hq) (hqleh 0).
Proof.
  split.
  intros (x,Hx) (y,Hy) ; simpl pr1.
  now apply (hq0lehandplus x y Hx Hy).
  apply isreflhqleh.
Defined.
Local Definition hnnq_mult_submonoid : issubmonoid (X := fld_to_multmonoid hq) (hqleh 0).
Proof.
  split.
  intros (x,Hx) (y,Hy) ; simpl pr1.
  apply (hqmultgeh0geh0 Hx Hy).
  now apply hqlthtoleh, hq1_gt0.
Defined.

Local Definition hnnq_subrigs : issubrig (X := hq) (hqleh 0).
Proof.
  split.
  apply hnnq_plus_submonoid.
  apply hnnq_mult_submonoid.
Defined.
Local Definition hnnq_commrig : commrig.
Proof.
  apply (carrierofasubcommrig (X := hq)).
  eexists.
  apply hnnq_subrigs.
Defined.

Local Definition hnnq_commrig_to_def : hnnq_commrig -> hnnq_def := 
  fun X : hnnq_commrig =>
    match X with
    | tpair _ r Hr => tpair (fun x : hq => 0 <= x) r Hr
    end.

Transparent hq.
Lemma hnnq_inv_ge0 (x : hnnq_commrig) : 0 <= / pr1 x.
Proof.
  intros (x,Hx) ; simpl pr1.
  destruct (isdecrelhqeq x 0) as [Hx0 | Hx0] ; simpl in Hx0.
  - rewrite Hx0, hqinv0.
    apply hqlthtoleh, hq1_gt0.
  - apply hqlehandmultlinv with x.
    + apply hqneqchoice in Hx0.
      destruct Hx0 as [Hx0 | Hx0].
      * exact Hx0.
      * now apply fromempty, Hx, Hx0.
    + rewrite hqmultx0.
      rewrite (hqisrinvmultinv _ Hx0).
      now apply hqlthtoleh, hq1_gt0.
Qed.
Local Definition hnnq_inv (x : hnnq_commrig) : hnnq_commrig := hq_to_hnnq_def (/ (pr1 x)) (hnnq_inv_ge0 x).

(** * Exportable definitions and theorems *)

Definition NonnegativeRationals : commrig := hnnq_commrig.
Definition NonnegativeRationals_to_Rationals : NonnegativeRationals -> hq :=
  pr1.
Definition Rationals_to_NonnegativeRationals (r : hq) (Hr : hqleh 0%hq r) : NonnegativeRationals :=
  tpair (fun x : hq => hqleh 0%hq x) r Hr.

Delimit Scope NnR_scope with NnR.


(** ** Order *)

Definition leNonnegativeRationals : po NonnegativeRationals :=
  popair hnnq_le isPartialOrder_hnnq_le.
Definition geNonnegativeRationals : po NonnegativeRationals :=
  popair hnnq_ge isPartialOrder_hnnq_ge.
Definition ltNonnegativeRationals : StrictPartialOrder NonnegativeRationals :=
  pairStrictPartialOrder hnnq_lt isStrictPartialOrder_hnnq_lt.
Definition gtNonnegativeRationals : StrictPartialOrder NonnegativeRationals :=
  pairStrictPartialOrder hnnq_gt isStrictPartialOrder_hnnq_gt.

Notation "x <= y" := (leNonnegativeRationals x y) : NnR_scope.
Notation "x >= y" := (geNonnegativeRationals x y) : NnR_scope.
Notation "x < y" := (ltNonnegativeRationals x y) : NnR_scope.
Notation "x > y" := (gtNonnegativeRationals x y) : NnR_scope.

(** ** Constants and Functions *)

Definition zeroNonnegativeRationals : NonnegativeRationals := 0%rig.
Definition oneNonnegativeRationals : NonnegativeRationals := 1%rig.

Definition plusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  (x + y)%rig.
Definition multNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  (x * y)%rig.

Notation "0" := zeroNonnegativeRationals : NnR_scope.
Notation "1" := oneNonnegativeRationals : NnR_scope.
Notation "x + y" := (plusNonnegativeRationals x y) : NnR_scope.
Notation "x * y" := (multNonnegativeRationals x y) : NnR_scope.

(** ** Theorems *)

Open Scope NnR_scope.

Lemma lt_leNonnegativeRationals :
  forall x y : NonnegativeRationals, x < y -> x <= y.
Proof.
  intros x y.
  now apply hqlthtoleh.
Qed.
Lemma notge_ltNonnegativeRationals :
  forall x y : NonnegativeRationals, neg (x >= y) -> x < y.
Proof.
  intros x y Hxy.
  now apply neghqgehtolth.
Qed.
Lemma istrans_ltNonnegativeRationals : istrans ltNonnegativeRationals.
Proof.
  now destruct ltNonnegativeRationals as (lt,(Htrans,H)) ; simpl.
Qed.
Lemma istrans_le_lt_ltNonnegativeRationals :
  forall x y z : NonnegativeRationals,
    x <= y -> y < z -> x < z.
Proof.
  intros x y z.
  now apply hqlehlthtrans.
Qed.
Lemma between_ltNonnegativeRationals :
  forall x y : NonnegativeRationals,
    x < y -> total2 (fun t => dirprod (x < t) (t < y)).
Proof.
  intros x y H.
  destruct (hqlth_between (pr1 x) (pr1 y) H) as [z (Hxz,Hzy)].
  assert (Hz : hqleh 0%hq z).
  { apply istranshqleh with (pr1 x). 
    now apply (pr2 x).
    apply (hqlthtoleh (pr1 x) z), Hxz. }
  exists (hq_to_hnnq_def z Hz).
  split.
  exact Hxz.
  exact Hzy.
Qed.

Lemma isnonnegative_NonnegativeRationals :
  forall x : NonnegativeRationals , 0 <= x.
Proof.
  intros x.
  apply (pr2 x).
Qed.

Close Scope NnR_scope.

(** ** Opacify *)

Global Opaque NonnegativeRationals.
Global Opaque leNonnegativeRationals geNonnegativeRationals.
Global Opaque ltNonnegativeRationals gtNonnegativeRationals.
Global Opaque zeroNonnegativeRationals plusNonnegativeRationals.

(* End of the file hnnq.v *)
