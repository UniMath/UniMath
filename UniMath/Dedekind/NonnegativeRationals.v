(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Fields_comp.
Require Import UniMath.Dedekind.DivisionRig.
Require Import UniMath.Dedekind.Complements.

Opaque hq.

Open Scope hq_scope.

(** ** Definition of non-negative rational numbers *)

Definition hnnq_set := subset (hqleh 0).

Local Definition hnnq_set_to_hq (r : hnnq_set) : hq := pr1 r.
Coercion hnnq_set_to_hq : pr1hSet >-> pr1hSet.
Local Definition hq_to_hnnq_set (r : hq) (Hr : hqleh 0 r) : hnnq_set :=
  r ,, Hr.

Definition hnnq_zero: hnnq_set := hq_to_hnnq_set 0 (isreflhqleh 0).
Definition hnnq_one: hnnq_set := hq_to_hnnq_set 1 (hqlthtoleh 0 1 hq1_gt0).
Definition hnnq_plus: binop hnnq_set := 
  λ x y : hnnq_set, hq_to_hnnq_set (pr1 x + pr1 y) (hq0lehandplus _ _ (pr2 x) (pr2 y)).
Definition hnnq_minus: binop hnnq_set := 
  λ x y : hnnq_set,
          match (hqgthorleh (pr1 y) (pr1 x)) with
          | ii1 _ => hnnq_zero
          | ii2 H => hq_to_hnnq_set (pr1 x - pr1 y) (hq0leminus _ _ H)
          end.
Definition hnnq_mult: binop hnnq_set := 
  λ x y : hnnq_set, hq_to_hnnq_set (pr1 x * pr1 y) (hqmultgeh0geh0 (pr2 x) (pr2 y)).
Definition hnnq_inv: unop hnnq_set := 
  λ x : hnnq_set,
        match (hqlehchoice 0 (pr1 x) (pr2 x)) with
        | ii1 Hx0 => hq_to_hnnq_set (/ pr1 x) (hqlthtoleh 0 (/ pr1 x) (hqinv_gt0 (pr1 x) Hx0))
        | ii2 _ => x
        end.
Definition hnnq_div : binop hnnq_set := λ x y : hnnq_set, hnnq_mult x (hnnq_inv y).

(** ** Equality and order on non-negative rational numbers *)

(** *** Order *)

Local Definition hnnq_le : hrel hnnq_set := resrel hqleh (hqleh 0).
Lemma isPartialOrder_hnnq_le : ispo hnnq_le.
Proof.
  split.
 intros x y z.
  now apply istranshqleh.
  intros x.
  now apply isreflhqleh.
Qed.  
  
Local Definition hnnq_ge : hrel hnnq_set := resrel hqgeh (hqleh 0).

Lemma isPartialOrder_hnnq_ge : ispo hnnq_ge.
Proof.
  destruct isPartialOrder_hnnq_le as [Htrans Hrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hrefl.
Qed.

Local Definition hnnq_lt : hrel hnnq_set := resrel hqlth (hqleh 0).
Lemma isStrongOrder_hnnq_lt : isStrongOrder hnnq_lt.
Proof.
  split.
  intros x y z.
  now apply istranshqlth.
  intros x.
  now apply isirreflhqlth.
Qed.

Local Definition hnnq_gt : hrel hnnq_set := resrel hqgth (hqleh 0).
Lemma isStrongOrder_hnnq_gt : isStrongOrder hnnq_gt.
Proof.
  destruct isStrongOrder_hnnq_lt as [Htrans Hirrefl].
  split.
  intros x y z Hxy Hyz.
  now apply Htrans with y.
  intros x.
  now apply Hirrefl.
Qed.

Lemma isEffectiveOrder_hnnq : isEffectiveOrder hnnq_le hnnq_lt.
Proof.
  split ; split.
  - exact isPartialOrder_hnnq_le.
  - exact isStrongOrder_hnnq_lt.
  - intros x y.
    now apply hqlthtoleh.
  - intros x y.
    now apply hqlehtoneghqgth.
Qed.

(** ** hnnq is a half field *)

Lemma iscomm_hnnq_plus:
  iscomm hnnq_plus.
Proof.
  intros (x,Hx) (y,Hy).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqpluscomm.
Qed.
Lemma isassoc_hnnq_plus :
  isassoc hnnq_plus.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqplusassoc.
Qed.
Lemma islunit_hnnq_zero_plus:
  islunit hnnq_plus hnnq_zero.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqplusl0.
Qed.
Lemma isrunit_hnnq_zero_plus:
  isrunit hnnq_plus hnnq_zero.
Proof.
  intros x.
  rewrite iscomm_hnnq_plus.
  now apply islunit_hnnq_zero_plus.
Qed.
Lemma iscomm_hnnq_mult:
  iscomm hnnq_mult.
Proof.
  intros (x,Hx) (y,Hy).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqmultcomm.
Qed.
Lemma isassoc_hnnq_mult:
  isassoc hnnq_mult.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqmultassoc.
Qed.
Lemma islunit_hnnq_one_mult:
  islunit hnnq_mult hnnq_one.
Proof.
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqmultl1.
Qed.
Lemma isrunit_hnnq_one_mult:
  isrunit hnnq_mult hnnq_one.
Proof.
  intros x.
  rewrite iscomm_hnnq_mult.
  now apply islunit_hnnq_one_mult.
Qed.
Lemma islinv'_hnnq_inv:
  islinv' hnnq_one hnnq_mult (hnnq_lt hnnq_zero)
          (λ x : subset (hnnq_lt hnnq_zero), hnnq_inv (pr1 x)).
Proof.
  intros (x,Hx) Hx0.
  unfold hnnq_inv.
  destruct hqlehchoice as [Hx0' | Hx0'] ; simpl in Hx0'.
  - apply total2_paths_second_isaprop; simpl pr1.
    + now apply pr2.
    + apply hqislinvmultinv.
      now apply hqgth_hqneq.
  - apply pathsinv0 in Hx0'.
    apply fromempty ; revert Hx0'.
    apply hqgth_hqneq, Hx0.
Qed.
Lemma isrinv'_hnnq_inv:
 isrinv' hnnq_one hnnq_mult (hnnq_lt hnnq_zero)
         (λ x : subset (hnnq_lt hnnq_zero), hnnq_inv (pr1 x)).
Proof.
  intros x Hx.
  rewrite iscomm_hnnq_mult.
  now apply islinv'_hnnq_inv.
Qed.
Lemma isldistr_hnnq_plus_mult:
  isldistr hnnq_plus hnnq_mult.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqldistr.
Qed.
Lemma isrdistr_hnnq_plus_mult:
  isrdistr hnnq_plus hnnq_mult.
Proof.
  intros x y z.
  rewrite !(iscomm_hnnq_mult _ z).
  now apply isldistr_hnnq_plus_mult.
Qed.
Lemma isDivRig_hnnq:
  isDivRig hnnq_zero hnnq_one hnnq_plus hnnq_mult 
              (hnnq_lt hnnq_zero) (λ x, hnnq_inv (pr1 x)).
Proof.
  repeat split.
  - exact isassoc_hnnq_plus.
  - exact islunit_hnnq_zero_plus.
  - exact isrunit_hnnq_zero_plus.
  - exact iscomm_hnnq_plus.
  - exact isassoc_hnnq_mult.
  - exact islunit_hnnq_one_mult.
  - exact isrunit_hnnq_one_mult.
  - exact islinv'_hnnq_inv.
  - exact isrinv'_hnnq_inv.
  - exact iscomm_hnnq_mult.
  - exact isldistr_hnnq_plus_mult.
  - exact isrdistr_hnnq_plus_mult.
Qed.
Definition DivRig_hnnq : DivRig := 
  isDivRig_DivRig hnnq_zero hnnq_one hnnq_plus hnnq_mult
                        (hnnq_lt hnnq_zero) (λ x : subset (hnnq_lt hnnq_zero), hnnq_inv (pr1 x))
                        isDivRig_hnnq.

(** * Exportable definitions and theorems *)

Definition NonnegativeRationals : DivRig := DivRig_hnnq.
Definition NonnegativeRationals_to_Rationals : NonnegativeRationals -> hq :=
  pr1.
Definition Rationals_to_NonnegativeRationals (r : hq) (Hr : hqleh 0%hq r) : NonnegativeRationals :=
  tpair _ r Hr.

Delimit Scope NRat_scope with NRat.

(** ** Order *)

Lemma isdeceq_NonnegativeRationals : isdeceq NonnegativeRationals.
Proof.
  intros (x,Hx) (y,Hy).
  destruct (isdeceqhq x y).
  - left.
    apply total2_paths_second_isaprop; simpl pr1.
    + now apply pr2.
    + exact p.
  - right.
    intro ; apply e.
    revert X.
    apply base_paths.
Qed.

Local Definition NonnegativeRationals_EffectivelyOrderedSet :=
  @pairEffectivelyOrderedSet NonnegativeRationals (pairEffectiveOrder _ _ isEffectiveOrder_hnnq).

Definition leNonnegativeRationals : po NonnegativeRationals :=
  @EOle NonnegativeRationals_EffectivelyOrderedSet.
Definition geNonnegativeRationals : po NonnegativeRationals :=
  @EOge NonnegativeRationals_EffectivelyOrderedSet.
Definition ltNonnegativeRationals : StrongOrder NonnegativeRationals :=
  @EOlt NonnegativeRationals_EffectivelyOrderedSet.
Definition gtNonnegativeRationals : StrongOrder NonnegativeRationals :=
  @EOgt NonnegativeRationals_EffectivelyOrderedSet.

Notation "x <= y" := (leNonnegativeRationals x y) : NRat_scope.
Notation "x >= y" := (geNonnegativeRationals x y) : NRat_scope.
Notation "x < y" := (ltNonnegativeRationals x y) : NRat_scope.
Notation "x > y" := (gtNonnegativeRationals x y) : NRat_scope.

(** ** Constants and Functions *)

Definition zeroNonnegativeRationals : NonnegativeRationals := hnnq_zero.
Definition oneNonnegativeRationals : NonnegativeRationals := hnnq_one.

Definition plusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_plus x y.
Definition minusNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_minus x y.
Definition multNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_mult x y.
Definition invNonnegativeRationals (x : NonnegativeRationals) : NonnegativeRationals :=
  hnnq_inv x.
Definition divNonnegativeRationals (x y : NonnegativeRationals) : NonnegativeRationals :=
  multNonnegativeRationals x (invNonnegativeRationals y).

Notation "0" := zeroNonnegativeRationals : NRat_scope.
Notation "1" := oneNonnegativeRationals : NRat_scope.
Notation "x + y" := (plusNonnegativeRationals x y) : NRat_scope.
Notation "x - y" := (minusNonnegativeRationals x y) : NRat_scope.
Notation "x * y" := (multNonnegativeRationals x y) : NRat_scope.
Notation "/ x" := (invNonnegativeRationals x) : NRat_scope.
Notation "x / y" := (divNonnegativeRationals x y) : NRat_scope.

Open Scope NRat_scope.

(** *** Correctness *)

Lemma zeroNonnegativeRationals_correct :
  0 = Rationals_to_NonnegativeRationals 0%hq (isreflhqleh 0%hq).
Proof.
  apply total2_paths_isaprop.
  - now intro ; apply pr2.
  - reflexivity.
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

Lemma NonnegativeRationals_eq0_le0 :
  forall r : NonnegativeRationals, (r = 0) = (r <= 0).
Proof.
  intro r.
  apply FunctionalExtensionality.weqtopaths.
  assert (H0 : isisolated NonnegativeRationals 0).
  intro.
  apply isdeceq_NonnegativeRationals.
  generalize (isaproppathstoisolated _ 0 H0 r) ; intro H.
  apply (logeqweq (hProppair _ H)).
  - intros Hr.
    rewrite Hr.
    apply isrefl_po.
  - intros Hr0.
    apply total2_paths_second_isaprop.
    + apply pr2.
    + apply isantisymmhqleh.
      apply Hr0.
      apply (pr2 r).
Qed.
Lemma NonnegativeRationals_neq0_gt0 :
  forall r : NonnegativeRationals, (r != 0) = (0 < r).
Proof.
  intros r.
  rewrite NonnegativeRationals_eq0_le0.
  apply FunctionalExtensionality.weqtopaths.
  apply (logeqweq (hProppair _ (isapropneg _))).
  now apply neghqlehtogth.
  now apply hqgthtoneghqleh.
Qed.

(** *** Order *)

Lemma isdecrel_leNonnegativeRationals : isdecrel leNonnegativeRationals.
Proof.
  intros x y.
  destruct (isdecrelhqleh (pr1 x) (pr1 y)) as [H | H].
  now left.
  now right.
Qed.

Definition isrefl_leNonnegativeRationals:
  ∀ x : NonnegativeRationals, x <= x :=
  isrefl_po _.
Definition istrans_leNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x <= y -> y <= z -> x <= z :=
  istrans_po _.
Definition lt_leNonnegativeRationals :
  forall x y : NonnegativeRationals, x < y -> x <= y :=
  @EOlt_EOle NonnegativeRationals_EffectivelyOrderedSet.
Lemma notge_ltNonnegativeRationals :
  forall x y : NonnegativeRationals, neg (x >= y) -> x < y.
Proof.
  intros x y Hxy.
  now apply neghqgehtolth.
Qed.
Definition istrans_ltNonnegativeRationals : istrans ltNonnegativeRationals :=
  istrans_StrongOrder _.
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
  exists (hq_to_hnnq_set z Hz).
  split.
  exact Hxz.
  exact Hzy.
Qed.

(** *** Algebra *)

Definition isassoc_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x + y + z = x + (y + z) :=
  DivRig_isassoc_plus.
Definition islunit_zeroNonnegativeRationals:
  forall r : NonnegativeRationals, 0 + r = r :=
  DivRig_islunit_zero.
Definition isrunit_zeroNonnegativeRationals:
  forall r : NonnegativeRationals, r + 0 = r :=
  DivRig_isrunit_zero.
Definition iscomm_plusNonnegativeRationals:
  ∀ x y : NonnegativeRationals, x + y = y + x :=
  DivRig_iscomm_plus.
Definition isassoc_multNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x * y * z = x * (y * z) :=
  DivRig_isassoc_mult.
Definition islunit_oneNonnegativeRationals:
  ∀ x : NonnegativeRationals, 1 * x = x :=
  DivRig_islunit_one.
Definition isrunit_oneNonnegativeRationals:
  ∀ x : NonnegativeRationals, x * 1 = x :=
  DivRig_isrunit_one.
Definition islinv_NonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 < x -> / x * x = 1 :=
  DivRig_islinv'.
Definition isrinv_NonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 < x -> x * / x = 1 :=
  DivRig_isrinv'.
Definition iscomm_multNonnegativeRationals:
  ∀ x y : NonnegativeRationals, x * y = y * x :=
  DivRig_iscomm_mult.
Definition isldistr_mult_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, z * (x + y) = z * x + z * y :=
  DivRig_isldistr.
Definition isrdistr_mult_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, (x + y) * z = x * z + y * z :=
  DivRig_isrdistr.

Lemma multdivNonnegativeRationals :
  forall q r : NonnegativeRationals, 0 < r -> (r * (q / r)) = q.
Proof. (** todo generalize *)
  intros q r Hr0.
  unfold divNonnegativeRationals.
  rewrite iscomm_multNonnegativeRationals, isassoc_multNonnegativeRationals.
  rewrite islinv_NonnegativeRationals.
  now apply isrunit_oneNonnegativeRationals.
  exact Hr0.
Qed.
Lemma islabsorb_zero_multNonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 * x = 0.
Proof. (** todo generalize *)
  intros (x,Hx).
  apply total2_paths_second_isaprop ; simpl pr1.
  - now apply pr2.
  - now apply hqmult0x.
Qed.                                
Lemma israbsorb_zero_multNonnegativeRationals:
  ∀ x : NonnegativeRationals, x * 0 = 0.
Proof. (** todo generalize *)
  intros x.
  rewrite iscomm_multNonnegativeRationals.
  now apply islabsorb_zero_multNonnegativeRationals.
Qed.
Lemma multrle1NonnegativeRationals :
  forall q r : NonnegativeRationals, (q <= 1)%NRat -> (r * q <= r)%NRat.
Proof.
  intros q r Hq.
  destruct (isdeceq_NonnegativeRationals r 0) as [Hr0 | Hr0].
  - rewrite Hr0, islabsorb_zero_multNonnegativeRationals.
    apply isrefl_leNonnegativeRationals.
  - pattern r at 2.
    rewrite <- (isrunit_oneNonnegativeRationals r).
    apply hqlehandmultl.
    apply neghqlehtogth.
    intro ; apply Hr0.
    now rewrite NonnegativeRationals_eq0_le0.
    exact Hq.
Qed.
Lemma ledivle1NonnegativeRationals :
  forall q r : NonnegativeRationals, (r != 0) -> (q <= r)%NRat -> (q / r <= 1)%NRat.
Proof.
  intros (q,Hq) (r,Hr) Hr0 Hrq.
  unfold divNonnegativeRationals.
  apply hqlehandmultrinv with r.
  now rewrite NonnegativeRationals_neq0_gt0 in Hr0.
  unfold invNonnegativeRationals, multNonnegativeRationals, hnnq_inv, hnnq_mult.
  destruct hqlehchoice ; simpl pr1.
  rewrite hqmultassoc.
  rewrite hqislinvmultinv.
  now rewrite hqmultr1, hqmultl1.
  now apply hqgth_hqneq.
  apply fromempty, Hr0.
  apply pathsinv0.
  apply total2_paths_second_isaprop.
  now apply pr2.
  exact p.
Qed.

Lemma NonnegativeRationals_plusltcompat :
  forall x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x + y < x' + y'.
Proof.
  intros x x' y y' Hx Hy.
  apply istrans_ltNonnegativeRationals with (x + y').
  now apply hqlthandplusl.
  now apply hqlthandplusr.
Qed.
Lemma NonnegativeRationals_leplus_r :
  forall r q : NonnegativeRationals, (r <= r + q)%NRat.
Proof.
  intros r q.
  pattern r at 1.
  rewrite <- (isrunit_zeroNonnegativeRationals r).
  apply hqlehandplusl.
  apply (pr2 q).
Qed.
Lemma NonnegativeRationals_leplus_l :
  forall r q : NonnegativeRationals, (r <= q + r)%NRat.
Proof.
  intros r q.
  rewrite iscomm_plusNonnegativeRationals.
  now apply NonnegativeRationals_leplus_r.
Qed.
Lemma NonnegativeRationals_pluslecompat_r :
  forall r q n : NonnegativeRationals, (q <= n)%NRat -> (q + r <= n + r)%NRat.
Proof.
  intros r q n H.
  now apply hqlehandplusr.
Qed.
Lemma NonnegativeRationals_pluslecompat_l :
  forall r q n : NonnegativeRationals, (q <= n)%NRat -> (r + q <= r + n)%NRat.
Proof.
  intros r q n H.
  now apply hqlehandplusl.
Qed.
Lemma NonnegativeRationals_pluslecancel_r :
  forall r q n : NonnegativeRationals, (q + r <= n + r)%NRat -> (q <= n)%NRat.
Proof.
  intros r q n H.
  now apply hqlehandplusrinv with (pr1 r).
Qed.
Lemma NonnegativeRationals_pluslecancel_l :
  forall r q n : NonnegativeRationals, (r + q <= r + n)%NRat -> (q <= n)%NRat.
Proof.
  intros r q n H.
  now apply hqlehandpluslinv with (pr1 r).
Qed.
Lemma NonnegativeRationals_plusr_minus :
  forall q r : NonnegativeRationals, ((r + q) - q)%NRat = r.
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
  forall q r : NonnegativeRationals, ((q + r) - q)%NRat = r.
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

Close Scope NRat_scope.

(** ** Opacify *)

Global Opaque NonnegativeRationals.
Global Opaque leNonnegativeRationals geNonnegativeRationals.
Global Opaque ltNonnegativeRationals gtNonnegativeRationals.
Global Opaque zeroNonnegativeRationals plusNonnegativeRationals minusNonnegativeRationals.
Global Opaque oneNonnegativeRationals multNonnegativeRationals.
Global Opaque invNonnegativeRationals divNonnegativeRationals.

(* End of the file hnnq.v *)
