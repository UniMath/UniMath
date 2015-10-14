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
  tpair _ r Hr.

Local Definition hnnq_set : hSet := 
  hSetpair _ (isasetsubset pr1 isasethq (isinclpr1 (hqleh _) (λ x : hq, pr2 (0 <= x)))).

Lemma isdeceq_hnnq : isdeceq hnnq_def.
Proof.
  apply isdeceqinclb with pr1.
  apply isdeceqhq.
  apply isinclpr1.
  intro ; apply pr2.
Qed.

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
Lemma isStrongOrder_hnnq_lt : isStrongOrder hnnq_lt.
Proof.
  split.
  intros x y z.
  now apply istranshqlth.
  intros x.
  now apply isirreflhqlth.
Qed.

Local Definition hnnq_gt : hrel hnnq_def := resrel hqgth (hqleh 0).
Lemma isStrongOrder_hnnq_gt : isStrongOrder hnnq_gt.
Proof.
  destruct isStrongOrder_hnnq_lt as [Htrans Hirrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hirrefl.
Qed.

(** ** Non-negative rational numbers are a commutative rig *)

Local Definition hnnq_plus_submonoid : issubmonoid (X := fld_to_monoid1 hq) (hqleh 0).
Proof.
  split.
  intros (x,Hx) (y,Hy) ; simpl pr1.
  now apply (hq0lehandplus x y Hx Hy).
  apply isreflhqleh.
Defined.
Local Definition hnnq_mult_submonoid : issubmonoid (X := fld_to_monoid2 hq) (hqleh 0).
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
    | tpair _ r Hr => tpair _ r Hr
    end.

(** ** Constants *)

Local Definition hnnq_zero : hnnq_commrig := 0%rig.
Local Definition hnnq_one : hnnq_commrig := 1%rig.

Delimit Scope hnnq_scope with hnnq.

Notation "0" := hnnq_zero : hnnq_scope.
Notation "1" := hnnq_one : hnnq_scope.

(** ** Functions *)

Definition hnnq_minus (q r : hnnq_def) : hnnq_def.
Proof.
  intros (q,Hq) (r,Hr).
  destruct (hqgthorleh r q) as [H0 | H0].
  - exact hnnq_zero.
  - apply (hq_to_hnnq_def (q - r)).
    now apply hq0leminus.
Defined.
                                           
(** ** Multiplicative inverse and division *)

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
Local Definition hnnq_div (x y : hnnq_commrig) : hnnq_commrig := (x * (hnnq_inv y))%rig.

Lemma hnnq_inv_mult_l :
  forall r : hnnq_commrig, r != 0%hnnq -> ((hnnq_inv r) * r)%rig = 1%hnnq.
                                            
Admitted.

(** * Exportable definitions and theorems *)

Definition NonnegativeRationals : commrig := hnnq_commrig.
Definition NonnegativeRationals_to_Rationals : NonnegativeRationals -> hq :=
  pr1.
Definition Rationals_to_NonnegativeRationals (r : hq) (Hr : hqleh 0%hq r) : NonnegativeRationals :=
  tpair _ r Hr.

Delimit Scope NnR_scope with NnR.


(** ** Order *)

Definition leNonnegativeRationals : po NonnegativeRationals :=
  popair hnnq_le isPartialOrder_hnnq_le.
Definition geNonnegativeRationals : po NonnegativeRationals :=
  popair hnnq_ge isPartialOrder_hnnq_ge.
Definition ltNonnegativeRationals : StrongOrder NonnegativeRationals :=
  pairStrongOrder hnnq_lt isStrongOrder_hnnq_lt.
Definition gtNonnegativeRationals : StrongOrder NonnegativeRationals :=
  pairStrongOrder hnnq_gt isStrongOrder_hnnq_gt.

Notation "x <= y" := (leNonnegativeRationals x y) : NnR_scope.
Notation "x >= y" := (geNonnegativeRationals x y) : NnR_scope.
Notation "x < y" := (ltNonnegativeRationals x y) : NnR_scope.
Notation "x > y" := (gtNonnegativeRationals x y) : NnR_scope.

(** ** Constants and Functions *)

Definition zeroNonnegativeRationals : NonnegativeRationals := 0%rig.
Definition oneNonnegativeRationals : NonnegativeRationals := 1%rig.

Definition plusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  (x + y)%rig.
Definition minusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_minus x y.
Definition multNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  (x * y)%rig.
Definition invNonnegativeRationals (x : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_inv x.
Definition divNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_div x y.

Notation "0" := zeroNonnegativeRationals : NnR_scope.
Notation "1" := oneNonnegativeRationals : NnR_scope.
Notation "x + y" := (plusNonnegativeRationals x y) : NnR_scope.
Notation "x - y" := (minusNonnegativeRationals x y) : NnR_scope.
Notation "x * y" := (multNonnegativeRationals x y) : NnR_scope.
Notation "/ x" := (invNonnegativeRationals x) : NnR_scope.
Notation "x / y" := (divNonnegativeRationals x y) : NnR_scope.

Open Scope NnR_scope.

(** *** Correctness *)

Lemma zeroNonnegativeRationals_correct :
  0 = Rationals_to_NonnegativeRationals 0%hq (isreflhqleh 0%hq).
Proof.
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - reflexivity.
Qed.

Lemma hq1ge0 : (0 <= 1)%hq.
Proof.
  now apply hqlthtoleh, hq1_gt0.
Qed.
Lemma oneNonnegativeRationals_correct :
  1 = Rationals_to_NonnegativeRationals 1%hq hq1ge0.
Proof.
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - reflexivity.
Qed.
Lemma plusNonnegativeRationals_correct :
  forall x y : NonnegativeRationals,
    x + y = Rationals_to_NonnegativeRationals (pr1 x + pr1 y)%hq (hq0lehandplus _ _ (pr2 x) (pr2 y)).
Proof.
  intros (x,Hx) (y,Hy).
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - reflexivity.
Qed.
Lemma minusNonnegativeRationals_correct :
  forall (x y : NonnegativeRationals) (Hxy : y <= x), 
    x - y = Rationals_to_NonnegativeRationals (pr1 x - pr1 y)%hq (hq0leminus (pr1 y) (pr1 x) Hxy).
Proof.
  intros (x,Hx) (y,Hy) H ; simpl in H.
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - unfold minusNonnegativeRationals, hnnq_minus.
    destruct hqgthorleh.
    + now apply fromempty, H.
    + reflexivity.
Qed.

(** ** Theorems *)

Lemma isnonnegative_NonnegativeRationals :
  forall x : NonnegativeRationals , 0 <= x.
Proof.
  intros x.
  apply (pr2 x).
Qed.
Lemma isnonnegative_NonnegativeRationals' :
  forall x : NonnegativeRationals , neg (x < 0).
Proof.
  intros x.
  apply (pr2 x).
Qed.
Lemma NonnegativeRationals_le0_eq0 :
  forall r : NonnegativeRationals, r <= 0 -> r = 0.
Proof.
  intros (r,Hr) Hr0.
  apply total2_paths_isaprop.
  intro ; apply pr2.
  simpl.
  apply isantisymmhqleh.
  apply Hr0.
  apply Hr.
Qed.

(** *** Order *)

Definition istrans_leNonnegativeRationals : istrans leNonnegativeRationals :=
  istrans_po _.

Definition isdeceq_NonnegativeRationals : isdeceq NonnegativeRationals
  := isdeceq_hnnq.

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

(** *** Algebra *)

Definition isassoc_plusNonnegativeRationals : isassoc plusNonnegativeRationals :=
  rigassoc1 _.
Definition iscomm_plusNonnegativeRationals : iscomm plusNonnegativeRationals :=
  rigcomm1 _.
Definition isassoc_multNonnegativeRationals : isassoc multNonnegativeRationals :=
  rigassoc2 _.
Definition iscomm_multNonnegativeRationals : iscomm multNonnegativeRationals :=
  rigcomm2 _.
Definition isldistr_mult_plusNonnegativeRationals : isldistr plusNonnegativeRationals multNonnegativeRationals :=
  rigldistr _.
Definition isrdistr_mult_plusNonnegativeRationals : isrdistr plusNonnegativeRationals multNonnegativeRationals :=
  rigrdistr _.

Lemma multdivNonnegativeRationals :
  forall q r : NonnegativeRationals, (r != 0) -> (r * (q / r)) = q.
Proof.
  intros q r Hr0.
  unfold divNonnegativeRationals, hnnq_div.
  rewrite iscomm_multNonnegativeRationals, isassoc_multNonnegativeRationals.
  
Admitted.
Lemma multrle1NonnegativeRationals :
  forall q r : NonnegativeRationals, (q <= 1)%NnR -> (r * q <= r)%NnR.
Admitted.
Lemma ledivle1NonnegativeRationals :
  forall q r : NonnegativeRationals, (r != 0) -> (q <= r)%NnR -> (q / r <= 1)%NnR.
Admitted.

Lemma NonnegativeRationals_plus0r :
  forall r : NonnegativeRationals, r + 0 = r.
Admitted.
Lemma NonnegativeRationals_plus0l :
  forall r : NonnegativeRationals, 0 + r = r.
Admitted.
Lemma NonnegativeRationals_plusltcompat :
  forall x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x + y < x' + y'.
Admitted.
Lemma NonnegativeRationals_leplus_r :
  forall r q : NonnegativeRationals, (r <= r + q)%NnR.
Admitted.
Lemma NonnegativeRationals_leplus_l :
  forall r q : NonnegativeRationals, (r <= q + r)%NnR.
Admitted.
Lemma isdecrel_leNonnegativeRationals : isdecrel leNonnegativeRationals.
Admitted.
Lemma NonnegativeRationals_pluslecompat_r :
  forall r q n : NonnegativeRationals, (q <= n)%NnR -> (q + r <= n + r)%NnR.
Admitted.
Lemma NonnegativeRationals_pluslecompat_l :
  forall r q n : NonnegativeRationals, (q <= n)%NnR -> (r + q <= r + n)%NnR.
Admitted.
Lemma NonnegativeRationals_pluslecancel_r :
  forall r q n : NonnegativeRationals, (q + r <= n + r)%NnR -> (q <= n)%NnR.
Admitted.
Lemma NonnegativeRationals_pluslecancel_l :
  forall r q n : NonnegativeRationals, (r + q <= r + n)%NnR -> (q <= n)%NnR.
Admitted.
Lemma NonnegativeRationals_plusr_minus :
  forall q r : NonnegativeRationals, ((r + q) - q)%NnR = r.
Proof.
  intros (q,Hq) (r,Hr).
  rewrite (minusNonnegativeRationals_correct _ _ (NonnegativeRationals_leplus_l _ _)).
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - simpl pr1.
    unfold hqminus.
    now rewrite hqplusassoc, (hqpluscomm q), (hqlminus q), hqplusr0.
Qed.
Lemma NonnegativeRationals_plusl_minus :
  forall q r : NonnegativeRationals, ((q + r) - q)%NnR = r.
Proof.
  intros q r.
  rewrite iscomm_plusNonnegativeRationals.
  now apply NonnegativeRationals_plusr_minus.
Qed.
Lemma NonnegativeRationals_minusr_plus :
  forall q r : NonnegativeRationals,
    r <= q -> (q - r) + r = q.
Proof.
  intros (q,Hq) (r,Hr) H ; simpl in H.
  unfold minusNonnegativeRationals, hnnq_minus.
  destruct hqgthorleh as [H'|H'].
  - now apply fromempty, H.
  - apply total2_paths_isaprop.
    + intro ; apply pr2.
    + unfold hqminus ; simpl.
      now rewrite hqplusassoc, hqlminus, hqplusr0.
Qed.

Close Scope NnR_scope.

(** ** Opacify *)

Global Opaque NonnegativeRationals.
Global Opaque leNonnegativeRationals geNonnegativeRationals.
Global Opaque ltNonnegativeRationals gtNonnegativeRationals.
Global Opaque zeroNonnegativeRationals plusNonnegativeRationals minusNonnegativeRationals.
Global Opaque oneNonnegativeRationals multNonnegativeRationals.
Global Opaque invNonnegativeRationals divNonnegativeRationals.

(* End of the file hnnq.v *)
