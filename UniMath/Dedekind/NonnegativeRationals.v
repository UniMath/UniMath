(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.RationalNumbers.
Require Import UniMath.Dedekind.Complements.

Opaque hq.

Open Scope hq_scope.

(** ** Definition of non-negative rational numbers *)

Local Definition hnnq_def := total2 (hqleh 0).

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

(** *** Equality *)

Local Definition hnnq_eq ( x y : hnnq_set) : hProp := 
  hqeq (pr1 x) (pr1 y).
Lemma isdecrel_hnnq_eq : isdecrel hnnq_eq.
Proof.
  intros (r1,H1) (r2,H2).
  apply isdecrelhqeq.
Qed.
Local Definition hnnq_deceq : decrel hnnq_def :=
  tpair _ hnnq_eq isdecrel_hnnq_eq.

Local Definition hnnq_booleq := decreltobrel hnnq_deceq.

Local Definition hnnq_neq ( x y : hnnq_def ) : hProp := hProppair ( neg (hnnq_eq  x y ) ) ( isapropneg _  )  .
Local Definition isdecrel_hnnq_neq : isdecrel hnnq_neq  := isdecnegrel _ isdecrel_hnnq_eq . 
Local Definition hnnq_decneq : decrel hnnq_def := decrelpair isdecrel_hnnq_neq . 

Definition hnnq_boolneq := decreltobrel hnnq_decneq .

(** *** Order *)

Local Definition hnnq_le (x y : hnnq_set) : hProp := hqleh (pr1 x) (pr1 y).
Lemma isPartialOrder_hnnq_le : ispo hnnq_le.
Proof.
  split.
  intros x y z.
  now apply istranshqleh.
  intros x.
  now apply isreflhqleh.
Qed.  
  
Local Definition hnnq_ge (x y : hnnq_set) : hProp := hqgeh (pr1 x) (pr1 y).
Lemma isPartialOrder_hnnq_ge : ispo hnnq_ge.
Proof.
  destruct isPartialOrder_hnnq_le as [Htrans Hrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hrefl.
Qed.

Local Definition hnnq_lt (x y : hnnq_set) : hProp := hqlth (pr1 x) (pr1 y).
Lemma isStrictPartialOrder_hnnq_lt : isStrictPartialOrder hnnq_lt.
Proof.
  split.
  intros x y z.
  now apply istranshqlth.
  intros x.
  now apply isirreflhqlth.
Qed.

Local Definition hnnq_gt (x y : hnnq_set) : hProp := hqgth (pr1 x) (pr1 y).
Lemma isStrictPartialOrder_hnnq_gt : isStrictPartialOrder hnnq_gt.
Proof.
  destruct isStrictPartialOrder_hnnq_lt as [Htrans Hirrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hirrefl.
Qed.

(** ** Non-negative rational numbers are an abelian monoid *)

Local Definition hnnq_plus (x y : hnnq_set) : hnnq_set :=
  hq_to_hnnq_def ((pr1 x) + (pr1 y)) (hq0lehandplus (pr1 x) (pr1 y) (pr2 x) (pr2 y)).

Local Definition hnnq_setwithbinop : setwithbinop :=
  tpair _ hnnq_set hnnq_plus.

Lemma isassoc_hnnq_plus : isassoc hnnq_plus.
Proof.
  intros x y z.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusassoc (pr1 x) (pr1 y) (pr1 z)).
Qed.

Local Definition hnnq_0 : hnnq_setwithbinop :=
  hq_to_hnnq_def 0 (isreflhqleh 0).
Lemma islunit_hnnq_plus_hnnq_0 :
  islunit hnnq_plus hnnq_0.
Proof.
  intros x.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusl0 (pr1 x)).
Qed.
Lemma isrunit_hnnq_plus_hnnq_0 :
  isrunit hnnq_plus hnnq_0.
Proof.
  intros x.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  apply (hqplusr0 (pr1 x)).
Qed.

Lemma iscomm_hnnq_plus : iscomm hnnq_plus.
Proof.
  intros x y.
  apply total2_paths_isaprop.
  intro.
  now destruct (hqleh 0 a).
  now apply (hqpluscomm (pr1 x) (pr1 y)).
Qed.

Local Definition hnnq_abmonoid : abmonoid.
Proof.
  exists hnnq_setwithbinop.
  simpl.
  split.
  split.
  exact isassoc_hnnq_plus.
  exists hnnq_0.
  split.
  exact islunit_hnnq_plus_hnnq_0.
  exact isrunit_hnnq_plus_hnnq_0.
  exact iscomm_hnnq_plus.
Defined.

(** * Exportable definitions and theorems *)

Definition NonnegativeRationals : abmonoid := hnnq_abmonoid.
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

Definition zeroNonnegativeRationals : NonnegativeRationals :=
  unel NonnegativeRationals.
Definition plusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  op x y.

Notation "0" := zeroNonnegativeRationals : NnR_scope.
Notation "x + y" := (plusNonnegativeRationals x y) : NnR_scope.

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
  (*exists ((x+y)/2). need hqdiv*)
Admitted.

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
