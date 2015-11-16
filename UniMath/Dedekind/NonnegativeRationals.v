(** * Definition of non-negative rational numbers *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Import UniMath.Dedekind.Sets_comp.
Require Import UniMath.Dedekind.Fields_comp.
Require Export UniMath.Foundations.Algebra.DivisionRig.
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
          match (hqgthorleh (pr1 x) (pr1 y)) with
          | ii2 _ => hnnq_zero
          | ii1 H => hq_to_hnnq_set (pr1 x - pr1 y) (hq0leminus _ _ (hqlthtoleh _ _ H))
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
Lemma ispreorder_hnnq_le : ispreorder hnnq_le.
Proof.
  split.
 intros x y z.
  now apply istranshqleh.
  intros x.
  now apply isreflhqleh.
Qed.

Local Definition hnnq_ge : hrel hnnq_set := resrel hqgeh (hqleh 0).
Lemma ispreorder_hnnq_ge : ispreorder hnnq_ge.
Proof.
  destruct ispreorder_hnnq_le as [Htrans Hrefl].
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
  - exact ispreorder_hnnq_le.
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
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqpluscomm.
Qed.
Lemma isassoc_hnnq_plus :
  isassoc hnnq_plus.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqplusassoc.
Qed.
Lemma islunit_hnnq_zero_plus:
  islunit hnnq_plus hnnq_zero.
Proof.
  intros (x,Hx).
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
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
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqmultcomm.
Qed.
Lemma isassoc_hnnq_mult:
  isassoc hnnq_mult.
Proof.
  intros (x,Hx) (y,Hy) (z,Hz).
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqmultassoc.
Qed.
Lemma islunit_hnnq_one_mult:
  islunit hnnq_mult hnnq_one.
Proof.
  intros (x,Hx).
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
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
  - apply subtypeEquality; simpl pr1.
    + now intro ; apply pr2.
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
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqldistr.
Qed.
Lemma isrdistr_hnnq_plus_mult:
  isrdistr hnnq_plus hnnq_mult.
Proof.
  intros x y z.
  rewrite !(iscomm_hnnq_mult _ z).
  now apply isldistr_hnnq_plus_mult.
Qed.

Definition isabmonoidop_hnnq_plus: isabmonoidop hnnq_plus.
Proof.
  repeat split.
  - exact isassoc_hnnq_plus.
  - exists hnnq_zero ; split.
    + exact islunit_hnnq_zero_plus.
    + exact isrunit_hnnq_zero_plus.
  - exact iscomm_hnnq_plus.
Defined.
Definition ismonoidop_hnnq_mult : ismonoidop hnnq_mult.
Proof.
  split.
  - exact isassoc_hnnq_mult.
  - exists hnnq_one ; split.
    + exact islunit_hnnq_one_mult.
    + exact isrunit_hnnq_one_mult.
Defined.
Definition commrig_hnnq: commrig.
Proof.
  exists (hnnq_set,,hnnq_plus,,hnnq_mult).
  repeat split.
  - exists (isabmonoidop_hnnq_plus,,ismonoidop_hnnq_mult) ; split.
    + intro x.
      apply subtypeEquality.
      * now intro ; apply pr2.
      * apply hqmult0x.
    + intro x.
      apply subtypeEquality.
      * now intro ; apply pr2.
      * apply hqmultx0.
  - exact isldistr_hnnq_plus_mult.
  - exact isrdistr_hnnq_plus_mult.
  - exact iscomm_hnnq_mult.
Defined.
Definition CommDivRig_hnnq: CommDivRig.
Proof.
  exists commrig_hnnq.
  split.
  - intro H.
    apply base_paths in H.
    apply hqgth_hqneq in H.
    exact H.
    exact hq1_gt0.
  - intros x Hx.
    assert (Hx' : hnnq_lt hnnq_zero x).
    { apply neghqlehtogth.
      intro Hx0 ; apply Hx.
      apply subtypeEquality.
      - now intro ;apply pr2.
      - apply isantisymmhqleh.
        apply Hx0.
        apply (pr2 x). }
    exists (hnnq_inv x) ; split.
    + now apply (islinv'_hnnq_inv x Hx').
    + now apply (isrinv'_hnnq_inv x Hx').
Defined.

(** * Exportable definitions and theorems *)

Definition NonnegativeRationals : CommDivRig := CommDivRig_hnnq.
Definition NonnegativeRationals_to_Rationals : NonnegativeRationals -> hq :=
  pr1.
Definition Rationals_to_NonnegativeRationals (r : hq) (Hr : hqleh 0%hq r) : NonnegativeRationals :=
  tpair _ r Hr.

Delimit Scope NRat_scope with NRat.

(** ** Order *)

Lemma isdeceq_NonnegativeRationals : isdeceq NonnegativeRationals.
Proof.
  intros (x,Hx) (y,Hy).
  destruct (isdeceqhq x y) as [H|H].
  - left.
    apply subtypeEquality; simpl pr1.
    + now intro ; apply pr2.
    + exact H.
  - right.
    intros H0 ; apply H.
    revert H0.
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

Definition twoNonnegativeRationals : NonnegativeRationals :=
  Rationals_to_NonnegativeRationals 2 (hqlthtoleh _ _ hq2_gt0).

Notation "0" := zeroNonnegativeRationals : NRat_scope.
Notation "1" := oneNonnegativeRationals : NRat_scope.
Notation "2" := twoNonnegativeRationals : NRat_scope.

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
  apply subtypeEquality.
  - now intro ; apply pr2.
  - reflexivity.
Qed.
Lemma oneNonnegativeRationals_correct :
  1 = Rationals_to_NonnegativeRationals 1%hq hq1ge0.
Proof.
  apply subtypeEquality.
  - now intro ; apply pr2.
  - reflexivity.
Qed.
Lemma plusNonnegativeRationals_correct :
  ∀ x y : NonnegativeRationals,
    x + y = Rationals_to_NonnegativeRationals (pr1 x + pr1 y)%hq (hq0lehandplus _ _ (pr2 x) (pr2 y)).
Proof.
  intros (x,Hx) (y,Hy).
  apply subtypeEquality.
  - now intro ; apply pr2.
  - reflexivity.
Qed.
Lemma minusNonnegativeRationals_correct :
  ∀ (x y : NonnegativeRationals) (Hxy : y <= x),
    x - y = Rationals_to_NonnegativeRationals (pr1 x - pr1 y)%hq (hq0leminus (pr1 y) (pr1 x) Hxy).
Proof.
  intros (x,Hx) (y,Hy) H ; simpl in H.
  apply subtypeEquality.
  - now intro ; apply pr2.
  - unfold minusNonnegativeRationals, hnnq_minus.
    destruct hqgthorleh as [Hgt | Hle].
    + reflexivity.
    + simpl pr1.
      apply neghqlthtogeh in H.
      rewrite (isantisymmhqleh _ _ H Hle).
      now rewrite hqrminus.
Qed.

(** ** Theorems *)

Lemma isnonnegative_NonnegativeRationals :
  ∀ x : NonnegativeRationals , 0 <= x.
Proof.
  intros x.
  apply (pr2 x).
Qed.
Lemma isnonnegative_NonnegativeRationals' :
  ∀ x : NonnegativeRationals , neg (x < 0).
Proof.
  intros x.
  apply (pr2 x).
Qed.

Lemma NonnegativeRationals_eq0_le0 :
  ∀ r : NonnegativeRationals, (r = 0) = (r <= 0).
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
    apply subtypeEquality.
    + now intro ; apply pr2.
    + apply isantisymmhqleh.
      apply Hr0.
      apply (pr2 r).
Qed.
Lemma NonnegativeRationals_neq0_gt0 :
  ∀ r : NonnegativeRationals, (r != 0) = (0 < r).
Proof.
  intros r.
  rewrite NonnegativeRationals_eq0_le0.
  apply FunctionalExtensionality.weqtopaths.
  apply (logeqweq (hProppair _ (isapropneg _))).
  now apply neghqlehtogth.
  now apply hqgthtoneghqleh.
Qed.

Lemma ispositive_oneNonnegativeRationals : 0 < 1.
Proof.
  exact hq1_gt0.
Qed.
Lemma ispositive_twoNonnegativeRationals : 0 < 2.
Proof.
  exact hq2_gt0.
Qed.

(** *** Order *)

Definition lt_leNonnegativeRationals :
  ∀ x y : NonnegativeRationals, x < y -> x <= y :=
  @EOlt_EOle NonnegativeRationals_EffectivelyOrderedSet.

Definition isrefl_leNonnegativeRationals:
  ∀ x : NonnegativeRationals, x <= x :=
  isrefl_po _.
Definition istrans_leNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x <= y -> y <= z -> x <= z :=
  istrans_po _.
Definition isirrefl_ltNonnegativeRationals:
  ∀ x : NonnegativeRationals, ¬ (x < x) :=
  isirrefl_StrongOrder _.
Definition istrans_ltNonnegativeRationals : istrans ltNonnegativeRationals :=
  istrans_StrongOrder _.
Lemma istrans_lt_le_ltNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x < y -> y <= z -> x < z.
Proof.
  intros x y z.
  now apply hqlthlehtrans.
Qed.
Lemma istrans_le_lt_ltNonnegativeRationals :
  ∀ x y z : NonnegativeRationals,
    x <= y -> y < z -> x < z.
Proof.
  intros x y z.
  now apply hqlehlthtrans.
Qed.

Lemma isantisymm_leNonnegativeRationals : isantisymm leNonnegativeRationals.
Proof.
  intros x y Hle Hge.
  apply subtypeEquality_prop.
  now apply isantisymmhqleh.
Qed.

Lemma notge_ltNonnegativeRationals :
  ∀ x y : NonnegativeRationals, neg (x >= y) -> x < y.
Proof.
  intros x y Hxy.
  now apply neghqgehtolth.
Qed.
Lemma between_ltNonnegativeRationals :
  ∀ x y : NonnegativeRationals,
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

Lemma lt_gtNonnegativeRationals :
  ∀ x y : NonnegativeRationals, (x > y) = (y < x).
Proof.
  intros x y.
  now apply uahp ; intro H ; apply H.
Qed.
Lemma ltNonnegativeRationals_noteq :
  ∀ x y, x < y -> x ≠ y.
Proof.
  intros x y Hlt Heq.
  revert Hlt ; rewrite Heq.
  now apply isirrefl_ltNonnegativeRationals.
Qed.
Lemma gtNonnegativeRationals_noteq :
  ∀ x y, x > y -> x ≠ y.
Proof.
  intros x y Hgt Heq.
  revert Hgt ; rewrite Heq.
  now apply isirrefl_ltNonnegativeRationals.
Qed.

Lemma isdecrel_leNonnegativeRationals : isdecrel leNonnegativeRationals.
Proof.
  intros x y.
  apply isdecrelhqleh.
Qed.
Lemma isdecrel_ltNonnegativeRationals : isdecrel ltNonnegativeRationals.
Proof.
  intros x y.
  apply isdecrelhqlth.
Qed.

Lemma le_eqorltNonnegativeRationals :
  ∀ x y : NonnegativeRationals, x <= y -> (x = y) ⨿ (x < y).
Proof.
  intros x y Hle.
  destruct (isdecrel_leNonnegativeRationals y x).
  - left.
    now apply isantisymm_leNonnegativeRationals.
  - right.
    now apply notge_ltNonnegativeRationals.
Qed.
Lemma noteq_ltorgtNonnegativeRationals :
  ∀ x y : NonnegativeRationals, x ≠ y -> (x < y) ⨿ (x > y).
Proof.
  intros x y Hneq.
  destruct (isdecrel_leNonnegativeRationals x y) as [Hle|Hlt].
  - left.
    apply le_eqorltNonnegativeRationals in Hle.
    now destruct Hle.
  - right.
    now apply notge_ltNonnegativeRationals in Hlt.
Qed.
Lemma eq0orgt0NonnegativeRationals :
  ∀ x : NonnegativeRationals, (x = 0) ⨿ (0 < x).
Proof.
  intros x.
  destruct (le_eqorltNonnegativeRationals 0 x) as [Hx | Hx].
  now apply isnonnegative_NonnegativeRationals.
  rewrite Hx ; now left.
  now right.
Qed.

(** *** Algebra *)

Definition isassoc_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x + y + z = x + (y + z) :=
  CommDivRig_isassoc_plus.
Definition islunit_zeroNonnegativeRationals:
  ∀ r : NonnegativeRationals, 0 + r = r :=
  CommDivRig_islunit_zero.
Definition isrunit_zeroNonnegativeRationals:
  ∀ r : NonnegativeRationals, r + 0 = r :=
  CommDivRig_isrunit_zero.
Definition iscomm_plusNonnegativeRationals:
  ∀ x y : NonnegativeRationals, x + y = y + x :=
  CommDivRig_iscomm_plus.
Definition isassoc_multNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, x * y * z = x * (y * z) :=
  CommDivRig_isassoc_mult.
Definition islunit_oneNonnegativeRationals:
  ∀ x : NonnegativeRationals, 1 * x = x :=
  CommDivRig_islunit_one.
Definition isrunit_oneNonnegativeRationals:
  ∀ x : NonnegativeRationals, x * 1 = x :=
  CommDivRig_isrunit_one.
Definition islinv_NonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 < x -> / x * x = 1.
Proof.
  intros x.
  rewrite <- NonnegativeRationals_neq0_gt0.
  revert x.
  apply @CommDivRig_islinv.
Qed.
Definition isrinv_NonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 < x -> x * / x = 1.
Proof.
  intros x.
  rewrite <- NonnegativeRationals_neq0_gt0.
  revert x.
  apply @CommDivRig_isrinv.
Qed.
Definition iscomm_multNonnegativeRationals:
  ∀ x y : NonnegativeRationals, x * y = y * x :=
  CommDivRig_iscomm_mult.
Definition isldistr_mult_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, z * (x + y) = z * x + z * y :=
  CommDivRig_isldistr.
Definition isrdistr_mult_plusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, (x + y) * z = x * z + y * z :=
  CommDivRig_isrdistr.
Lemma islabsorb_zero_multNonnegativeRationals:
  ∀ x : NonnegativeRationals, 0 * x = 0.
Proof. (** todo generalize *)
  intros (x,Hx).
  apply subtypeEquality ; simpl pr1.
  - now intro ; apply pr2.
  - now apply hqmult0x.
Qed.
Lemma israbsorb_zero_multNonnegativeRationals:
  ∀ x : NonnegativeRationals, x * 0 = 0.
Proof. (** todo generalize *)
  intros x.
  rewrite iscomm_multNonnegativeRationals.
  now apply islabsorb_zero_multNonnegativeRationals.
Qed.

(** Theorems about multiplication and inverse *)

Lemma multNonnegativeRationals_lt_l :
  ∀ k x y, 0 < k -> (k * x < k * y) = (x < y).
Proof.
  intros k x y Hk.
  apply uahp ; intro H.
  - apply (hqlthandmultlinv (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
  - apply (hqlthandmultl (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
Qed.
Lemma multNonnegativeRationals_lt_r :
  ∀ k x y, 0 < k -> (x * k < y * k) = (x < y).
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_lt_l.
Qed.
Lemma multNonnegativeRationals_le_l :
  ∀ k x y, 0 < k -> (k * x <= k * y) = (x <= y).
Proof.
  intros k x y Hk.
  apply uahp ; intro H.
  - apply (hqlehandmultlinv (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
  - apply (hqlehandmultl (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
Qed.
Lemma multNonnegativeRationals_le_l' :
  ∀ k x y, (x <= y) -> (k * x <= k * y).
Proof.
  intros k x y Hle.
  destruct (eq0orgt0NonnegativeRationals k) as [Hx0 | Hx0].
  rewrite Hx0.
  rewrite !islabsorb_zero_multNonnegativeRationals.
  now apply isrefl_leNonnegativeRationals.
  now rewrite multNonnegativeRationals_le_l.
Qed.
Lemma multNonnegativeRationals_le_r :
  ∀ k x y, 0 < k -> (x * k <= y * k) = (x <= y).
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_le_l.
Qed.
Lemma multNonnegativeRationals_le_r' :
  ∀ k x y,  (x <= y) -> (x * k <= y * k).
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_le_l'.
Qed.

Lemma ispositive_multNonnegativeRationals:
  ∀ x y : NonnegativeRationals,
    0 < x -> 0 < y -> 0 < x * y.
Proof.
  intros x y Hx Hy.
  now rewrite <- (israbsorb_zero_multNonnegativeRationals x), multNonnegativeRationals_lt_l.
Qed.
Lemma multNonnegativeRationals_lt:
  ∀ x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x * y < x' * y'.
Proof.
  intros x x' y y' Hx Hy.
  destruct (eq0orgt0NonnegativeRationals x) as [Hx0 | Hx0].
  - rewrite Hx0, islabsorb_zero_multNonnegativeRationals.
    apply ispositive_multNonnegativeRationals.
    rewrite <- Hx0 ; exact Hx.
    apply istrans_le_lt_ltNonnegativeRationals with (2 := Hy).
    now apply isnonnegative_NonnegativeRationals.
  - apply istrans_lt_le_ltNonnegativeRationals with (x * y').
    now rewrite multNonnegativeRationals_lt_l.
    apply multNonnegativeRationals_le_r'.
    now apply lt_leNonnegativeRationals.
Qed.
Lemma invNonnegativeRationals_pos :
  ∀ x, (0 < / x) = (0 < x).
Proof.
  intros x.
  apply uahp ; intro Hx.
  - rewrite <- (multNonnegativeRationals_lt_r _ _ _ Hx),
    islabsorb_zero_multNonnegativeRationals,
    isrinv_NonnegativeRationals.
    + exact ispositive_oneNonnegativeRationals.
    + rewrite <- NonnegativeRationals_neq0_gt0 ; intros Hx0.
      revert Hx ; rewrite Hx0.
      unfold invNonnegativeRationals, hnnq_inv.
      destruct hqlehchoice as [Hx | Hx].
      * apply fromempty ; revert Hx.
        now apply isirreflhqlth.
      * now apply isirrefl_ltNonnegativeRationals.
  - rewrite <- (multNonnegativeRationals_lt_l _ _ _ Hx),
    israbsorb_zero_multNonnegativeRationals,
    isrinv_NonnegativeRationals.
    + exact ispositive_oneNonnegativeRationals.
    + rewrite <- NonnegativeRationals_neq0_gt0 ; intros Hx0.
      revert Hx ; rewrite Hx0.
      now apply isirrefl_ltNonnegativeRationals.
Qed.

Lemma ispositive_divNonnegativeRationals :
  ∀ x y, 0 < x -> 0 < y -> 0 < x / y.
Proof.
  intros x y Hx Hy.
  apply ispositive_multNonnegativeRationals.
  exact Hx.
  now rewrite invNonnegativeRationals_pos.
Qed.

Lemma multdivNonnegativeRationals :
  ∀ q r : NonnegativeRationals, 0 < r -> (r * (q / r)) = q.
Proof. (** todo generalize *)
  intros q r Hr0.
  unfold divNonnegativeRationals.
  rewrite iscomm_multNonnegativeRationals, isassoc_multNonnegativeRationals.
  rewrite islinv_NonnegativeRationals.
  now apply isrunit_oneNonnegativeRationals.
  exact Hr0.
Qed.

Lemma NQhalf_is_pos : ∀ x, (0 < x) = (0 < x / 2).
Proof.
  intro x.
  apply uahp ; intro Hx.
  - rewrite <- (multNonnegativeRationals_lt_r 2).
    unfold divNonnegativeRationals ;
      rewrite isassoc_multNonnegativeRationals, islabsorb_zero_multNonnegativeRationals.
    rewrite islinv_NonnegativeRationals.
    now rewrite isrunit_oneNonnegativeRationals.
    now apply ispositive_twoNonnegativeRationals.
    now apply ispositive_twoNonnegativeRationals.
  - rewrite <- (multNonnegativeRationals_lt_r (/2)).
    rewrite islabsorb_zero_multNonnegativeRationals.
    exact Hx.
    rewrite invNonnegativeRationals_pos.
    now apply ispositive_twoNonnegativeRationals.
Qed.
Lemma NQhalf_double : ∀ x, x = x / 2 + x / 2.
Proof.
  intros (x,Hx).

  unfold divNonnegativeRationals, invNonnegativeRationals, hnnq_inv, twoNonnegativeRationals, Rationals_to_NonnegativeRationals ; simpl pr1.
  destruct hqlehchoice as [H2 | H2].
  apply subtypeEquality_prop ; simpl pr1.
  rewrite !(hqmultcomm x), <- hqldistr, hqmultcomm.
  apply hqplusdiv2.
  apply fromempty ; generalize hq2_gt0.
  rewrite H2.
  now apply (isirreflhqlth 2%hq).
Qed.
Lemma notlt_geNonnegativeRationals:
  ∀ x y : NonnegativeRationals, ¬ (x < y) -> x >= y.
Proof.
  intros x y.
  now apply neghqlthtogeh.
Qed.

Lemma multrle1NonnegativeRationals :
  ∀ q r : NonnegativeRationals, q <= 1 -> r * q <= r.
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
  ∀ q r : NonnegativeRationals, q <= r -> q / r <= 1.
Proof.
  intros q r Hrq.
  destruct (eq0orgt0NonnegativeRationals r) as [Hr0 | Hr0].
  - rewrite Hr0, <- NonnegativeRationals_eq0_le0 in Hrq.
    unfold divNonnegativeRationals.
    rewrite Hrq, islabsorb_zero_multNonnegativeRationals.
    now apply isnonnegative_NonnegativeRationals.
  - rewrite <- (multNonnegativeRationals_le_r r).
    unfold divNonnegativeRationals.
    rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals.
    now rewrite isrunit_oneNonnegativeRationals, islunit_oneNonnegativeRationals.
    exact Hr0.
    exact Hr0.
Qed.

Lemma NonnegativeRationals_plusltcompat :
  ∀ x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x + y < x' + y'.
Proof.
  intros x x' y y' Hx Hy.
  apply istrans_ltNonnegativeRationals with (x + y').
  now apply hqlthandplusl.
  now apply hqlthandplusr.
Qed.
Lemma NonnegativeRationals_leplus_r :
  ∀ r q : NonnegativeRationals, r <= r + q.
Proof.
  intros r q.
  pattern r at 1.
  rewrite <- (isrunit_zeroNonnegativeRationals r).
  apply hqlehandplusl.
  apply (pr2 q).
Qed.
Lemma NonnegativeRationals_leplus_l :
  ∀ r q : NonnegativeRationals, r <= q + r.
Proof.
  intros r q.
  rewrite iscomm_plusNonnegativeRationals.
  now apply NonnegativeRationals_leplus_r.
Qed.
Lemma NonnegativeRationals_pluslecompat_r :
  ∀ r q n : NonnegativeRationals, q <= n -> q + r <= n + r.
Proof.
  intros r q n H.
  now apply hqlehandplusr.
Qed.
Lemma NonnegativeRationals_pluslecompat_l :
  ∀ r q n : NonnegativeRationals, q <= n -> r + q <= r + n.
Proof.
  intros r q n H.
  now apply hqlehandplusl.
Qed.
Lemma NonnegativeRationals_pluslecancel_r :
  ∀ r q n : NonnegativeRationals, q + r <= n + r -> q <= n.
Proof.
  intros r q n H.
  now apply hqlehandplusrinv with (pr1 r).
Qed.
Lemma NonnegativeRationals_pluslecancel_l :
  ∀ r q n : NonnegativeRationals, r + q <= r + n -> q <= n.
Proof.
  intros r q n H.
  now apply hqlehandpluslinv with (pr1 r).
Qed.
Lemma NonnegativeRationals_plusr_minus :
  ∀ q r : NonnegativeRationals, (r + q) - q = r.
Proof.
  intros (q,Hq) (r,Hr).
  rewrite (minusNonnegativeRationals_correct _ _ (NonnegativeRationals_leplus_l _ _)).
  apply subtypeEquality.
  - now intro ; apply pr2.
  - simpl pr1.
    unfold hqminus.
    now rewrite hqplusassoc, (hqpluscomm q), (hqlminus q), hqplusr0.
Qed.
Lemma NonnegativeRationals_plusl_minus :
  ∀ q r : NonnegativeRationals, (q + r) - q = r.
Proof.
  intros q r.
  rewrite iscomm_plusNonnegativeRationals.
  now apply NonnegativeRationals_plusr_minus.
Qed.
Lemma minusNonegativeRationals_eq_zero:
  ∀ x y, x <= y -> x - y = 0.
Proof.
  intros (x,Hx) (y,Hy) Hle.
  unfold minusNonnegativeRationals, hnnq_minus ; simpl pr1.
  destruct hqgthorleh as [H | H].
  - now apply fromempty, Hle.
  - reflexivity.
Qed.
Lemma minusNonegativeRationals_plusr :
  ∀ q r : NonnegativeRationals,
    r <= q -> (q - r) + r = q.
Proof.
  intros (q,Hq) (r,Hr) H ; simpl in H.
  unfold minusNonnegativeRationals, hnnq_minus.
  destruct hqgthorleh as [H'|H'].
  - apply subtypeEquality_prop.
    unfold hqminus ; simpl.
    now rewrite hqplusassoc, hqlminus, hqplusr0.
  - apply subtypeEquality_prop ; simpl pr1.
    rewrite hqplusl0.
    now apply isantisymmhqleh.
Qed.
Lemma plusNonnegativeRationals_ltcompat_r :
  ∀ x y z, (y + x < z + x) = (y < z).
Proof.
  intros x y z.
  apply uahp.
  now apply hqlthandplusrinv.
  now apply hqlthandplusr.
Qed.
Lemma plusNonnegativeRationals_ltcompat_l :
  ∀ x y z, (x + y < x + z) = (y < z).
Proof.
  intros x y z.
  rewrite !(iscomm_plusNonnegativeRationals x).
  now apply plusNonnegativeRationals_ltcompat_r.
Qed.
Lemma minusNonnegativeRationals_gt0 : ∀ x y, (0 < y - x) = (x < y).
Proof.
  intros x y.
  apply uahp ; intro Hlt.
  - revert Hlt.
    unfold minusNonnegativeRationals, hnnq_minus.
    destruct hqgthorleh as [H0 | H0] ; intro Hlt.
    + exact H0.
    + now apply isirrefl_ltNonnegativeRationals in Hlt.
  - rewrite <- (plusNonnegativeRationals_ltcompat_r x).
    rewrite islunit_zeroNonnegativeRationals, minusNonegativeRationals_plusr.
    + exact Hlt.
    + now apply lt_leNonnegativeRationals.
Qed.

Lemma NonnegativeRationals_leminus :
  ∀ x y, x - y <= x.
Proof.
  intros x y.
  apply NonnegativeRationals_pluslecancel_r with y.
  destruct (isdecrel_leNonnegativeRationals y x) as [Hle | Hlt].
  - rewrite minusNonegativeRationals_plusr.
    now apply NonnegativeRationals_leplus_r.
    exact Hle.
  - rewrite minusNonegativeRationals_eq_zero.
    rewrite islunit_zeroNonnegativeRationals.
    apply NonnegativeRationals_leplus_l.
    apply lt_leNonnegativeRationals.
    now apply notge_ltNonnegativeRationals.
Qed.

Lemma le_geNonnegativeRationals:
  ∀ x y : NonnegativeRationals, (x >= y) = (y <= x).
Proof.
  reflexivity.
Qed.
Lemma one_lt_twoNonnegativeRationals : 1 < 2.
Proof.
  change (1 < 2)%hq.
  rewrite <- (hqplusr0 1%hq), hq2eq1plus1.
  apply hqlthandplusl.
  exact hq1_gt0.
Qed.
Lemma ispositive_plusNonnegativeRationals_l :
  forall x y : NonnegativeRationals, (0 < x)%NRat -> (0 < x + y)%NRat.
Proof.
  intros x y Hx.
  apply istrans_lt_le_ltNonnegativeRationals with (1 := Hx).
  now apply NonnegativeRationals_leplus_r.
Qed.
Lemma div_le_plusNonnegativeRationals :
  forall x y : NonnegativeRationals, / (x + y) <= / x + / y.
Proof.
  intros x y.
  destruct (eq0orgt0NonnegativeRationals x) as [Hx0 | Hx0].
  rewrite Hx0, islunit_zeroNonnegativeRationals ; clear Hx0 x.
  now apply NonnegativeRationals_leplus_l.
  destruct (eq0orgt0NonnegativeRationals y) as [Hy0 | Hy0].
  rewrite Hy0, isrunit_zeroNonnegativeRationals ; clear Hy0 y.
  now apply NonnegativeRationals_leplus_r.
  rewrite <- (multNonnegativeRationals_le_l _ _ _ Hx0), isldistr_mult_plusNonnegativeRationals, (isrinv_NonnegativeRationals _ Hx0), !(iscomm_multNonnegativeRationals x).
  rewrite <- (multNonnegativeRationals_le_l _ _ _ Hy0), isldistr_mult_plusNonnegativeRationals, <- (isassoc_multNonnegativeRationals _ (/ y)%NRat), (isrinv_NonnegativeRationals _ Hy0), islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals, (iscomm_multNonnegativeRationals y).
  rewrite <- (multNonnegativeRationals_le_l (x + y)), <- ! isassoc_multNonnegativeRationals , isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isldistr_mult_plusNonnegativeRationals, !isrdistr_mult_plusNonnegativeRationals, !isassoc_plusNonnegativeRationals.
  now apply NonnegativeRationals_leplus_r.
  now apply ispositive_plusNonnegativeRationals_l.
  now apply ispositive_plusNonnegativeRationals_l.
Qed.
Lemma div_leNonnegativeRationals :
  forall x y : NonnegativeRationals, 0 < x -> x <= y -> / y <= / x.
Proof.
  intros x y Hx0 Hxy.
  rewrite <- (multNonnegativeRationals_le_l x), isrinv_NonnegativeRationals.
  now apply ledivle1NonnegativeRationals.
  exact Hx0.
  exact Hx0.
Qed.
Lemma minus_leNonnegativeRationals_l :
  forall k x y : NonnegativeRationals, x <= y -> x - k <= y - k.
Proof.
  intros k x y Hxy.
  case (isdecrel_leNonnegativeRationals k x) ; intros Hkx.
  - apply (NonnegativeRationals_pluslecancel_r k).
    rewrite !minusNonegativeRationals_plusr.
    exact Hxy.
    now apply istrans_leNonnegativeRationals with (2 := Hxy).
    exact Hkx.
  - rewrite minusNonegativeRationals_eq_zero.
    now apply isnonnegative_NonnegativeRationals.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma minus_ltNonnegativeRationals_l' :
  forall x y z : NonnegativeRationals, x - z < y - z -> x < y.
Proof.
  intros x y z Hlt.
  assert (Hyz : (z < y)%NRat).
  { rewrite <- minusNonnegativeRationals_gt0.
    apply istrans_le_lt_ltNonnegativeRationals with (x - z).
    now apply isnonnegative_NonnegativeRationals.
    exact Hlt. }
  case (isdecrel_leNonnegativeRationals x z) ; intro Hxz.
  - apply istrans_le_lt_ltNonnegativeRationals with (1 := Hxz).
    exact Hyz.
  - apply notge_ltNonnegativeRationals, lt_leNonnegativeRationals in Hxz.
    apply lt_leNonnegativeRationals in Hyz.
    rewrite <- (minusNonegativeRationals_plusr _ _ Hxz), <- (minusNonegativeRationals_plusr _ _ Hyz).
    rewrite plusNonnegativeRationals_ltcompat_r.
    exact Hlt.
Qed.
Lemma inv_zeroNonnegativeRationals :
  / 0 = 0.
Proof.
  unfold zeroNonnegativeRationals, invNonnegativeRationals, hnnq_zero, hnnq_inv ; simpl pr1.
  case hqlehchoice ; intro H0.
  - now apply fromempty ; apply isirreflhqlth in H0.
  - reflexivity.
Qed.
Lemma isinvolutive_invNonnegativeRationals :
  forall x, (/ (/ x))%NRat = x.
Proof.
  intros x.
  case (eq0orgt0NonnegativeRationals x) ; intro Hx0.
  - now rewrite Hx0, !inv_zeroNonnegativeRationals.
  - generalize Hx0.
    rewrite <- invNonnegativeRationals_pos.
    unfold invNonnegativeRationals, hnnq_inv at 2.
    intro Hinvx0.
    destruct hqlehchoice as [Hinvx0' | Hinvx0'].
    + destruct x as (x,Hx).
      revert Hinvx0'.
      unfold hnnq_inv.
      simpl (hqlehchoice 0%hq (pr1 (x,, Hx)) (pr2 (x,, Hx))).
      destruct (hqlehchoice 0%hq x Hx) as [Hx0' | Hx0'] ; simpl pr1 ; intro Hinvx0'.
      * apply subtypeEquality_prop.
        simpl.
        apply hqmultrcan with (/ x)%hq.
        intro H.
        rewrite H in Hinvx0'.
        now apply (isirreflhqlth 0%hq), Hinvx0'.
        rewrite hqislinvmultinv, hqisrinvmultinv.
        reflexivity.
        intro H.
        rewrite H in Hx0'.
        now apply (isirreflhqlth 0%hq), Hx0'.
        intro H.
        rewrite H in Hinvx0'.
        now apply (isirreflhqlth 0%hq), Hinvx0'.
      * apply fromempty.
        rewrite <- Hx0' in Hinvx0'.
        now apply (isirreflhqlth 0%hq), Hinvx0'.
    + apply fromempty.
      revert Hinvx0' Hinvx0.
      destruct (hnnq_inv x) as (y,Hy) ; simpl pr1 ; intro Hy0 ; revert Hy.
      rewrite <- Hy0 ; intro Hy.
      now apply (isirreflhqlth 0%hq).
Qed.
Lemma NonnegativeRationals_ltplus_r :
  ∀ r q : NonnegativeRationals, (0 < q)%NRat -> (r < r + q)%NRat.
Proof.
  intros x y Hy0.
  pattern x at 1.
  rewrite <- (isrunit_zeroNonnegativeRationals x).
  rewrite plusNonnegativeRationals_ltcompat_l.
  exact Hy0.
Qed.
Lemma div_lt_plusNonnegativeRationals_l :
  forall x y : NonnegativeRationals, (0 < x)%NRat -> (0 < y)%NRat -> (/ (x + y) < / x + / y)%NRat.
Proof.
  intros x y Hx0 Hy0.
  rewrite <- (multNonnegativeRationals_lt_l _ _ _ Hx0), isldistr_mult_plusNonnegativeRationals, (isrinv_NonnegativeRationals _ Hx0), !(iscomm_multNonnegativeRationals x).
  rewrite <- (multNonnegativeRationals_lt_l _ _ _ Hy0), isldistr_mult_plusNonnegativeRationals, <- (isassoc_multNonnegativeRationals _ (/ y)%NRat), (isrinv_NonnegativeRationals _ Hy0), islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals, (iscomm_multNonnegativeRationals y).
  rewrite <- (multNonnegativeRationals_lt_l (x + y)), <- ! isassoc_multNonnegativeRationals , isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isldistr_mult_plusNonnegativeRationals, !isrdistr_mult_plusNonnegativeRationals, !isassoc_plusNonnegativeRationals.
  apply NonnegativeRationals_ltplus_r.
  apply ispositive_plusNonnegativeRationals_l.
  now apply ispositive_multNonnegativeRationals.
  now apply ispositive_plusNonnegativeRationals_l.
  now apply ispositive_plusNonnegativeRationals_l.
Qed.
Lemma multNonnegativeRationals_eq_l:
  ∀ k x y : NonnegativeRationals,
    (0 < k)%NRat -> (k * x = k * y) -> (x = y).
Proof.
  intros k x y Hk0 H.
  rewrite <- (islunit_oneNonnegativeRationals x).
  rewrite <- (islinv_NonnegativeRationals k).
  rewrite isassoc_multNonnegativeRationals.
  rewrite H.
  rewrite <- isassoc_multNonnegativeRationals.
  rewrite islinv_NonnegativeRationals.
  now apply islunit_oneNonnegativeRationals.
  exact Hk0.
  exact Hk0.
Qed.
Lemma multNonnegativeRationals_eq_r:
  ∀ k x y : NonnegativeRationals,
    (0 < k)%NRat -> (x * k = y * k) -> (x = y).
Proof.
  intros k x y Hk0.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_eq_l.
Qed.
Lemma plusNonnegativeRationals_eq_l:
  ∀ k x y : NonnegativeRationals,
    (k + x = k + y) -> (x = y).
Proof.
  intros k x y H.
  apply isantisymm_leNonnegativeRationals ;
    apply (NonnegativeRationals_pluslecancel_l k) ;
    rewrite H ;
    apply isrefl_leNonnegativeRationals.
Qed.
Lemma plusNonnegativeRationals_eq_r:
  ∀ k x y : NonnegativeRationals,
    (x + k = y + k) -> (x = y).
Proof.
  intros k x y.
  rewrite !(iscomm_plusNonnegativeRationals _ k).
  now apply plusNonnegativeRationals_eq_l.
Qed.
Lemma zero_minusNonnegativeRationals :
  forall x, (0 - x = 0)%NRat.
Proof.
  intros x.
  apply minusNonegativeRationals_eq_zero.
  now apply isnonnegative_NonnegativeRationals.
Qed.
Lemma isldistr_mult_minusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, z * (x - y) = z * x - z * y.
Proof.
  intros x y z.
  destruct (isdecrel_leNonnegativeRationals x y) as [Hle | Hlt].
  - rewrite !minusNonegativeRationals_eq_zero.
    now apply israbsorb_zero_multNonnegativeRationals.
    now apply multNonnegativeRationals_le_l', Hle.
    exact Hle.
  - apply notge_ltNonnegativeRationals, lt_leNonnegativeRationals in Hlt.
    apply plusNonnegativeRationals_eq_r with (z * y).
    rewrite <- isldistr_mult_plusNonnegativeRationals.
    rewrite !minusNonegativeRationals_plusr.
    reflexivity.
    now apply multNonnegativeRationals_le_l', Hlt.
    exact Hlt.
Qed.
Lemma isrdistr_mult_minusNonnegativeRationals:
  ∀ x y z : NonnegativeRationals, (x - y) * z = x * z - y * z.
Proof.
  intros x y z.
  rewrite !(iscomm_multNonnegativeRationals _ z).
  now apply isldistr_mult_minusNonnegativeRationals.
Qed.
Lemma minus_divNonnegativeRationals :
  forall x y : NonnegativeRationals, (0 < y)%NRat -> (/ x - / y = (y - x) / (x * y))%NRat.
Proof.
  intros x y Hy0.
  destruct (eq0orgt0NonnegativeRationals x) as [Hx0 | Hx0].
  - unfold divNonnegativeRationals.
    now rewrite Hx0, islabsorb_zero_multNonnegativeRationals, inv_zeroNonnegativeRationals, israbsorb_zero_multNonnegativeRationals, zero_minusNonnegativeRationals.
  - apply multNonnegativeRationals_eq_l with (x * y).
    now apply ispositive_multNonnegativeRationals.
    rewrite multdivNonnegativeRationals.
    2: now apply ispositive_multNonnegativeRationals.
    rewrite isldistr_mult_minusNonnegativeRationals.
    rewrite iscomm_multNonnegativeRationals, <- isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
    2: exact Hx0.
    now rewrite isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
Qed.

(** NQmax *)

Definition NQmax : binop NonnegativeRationals :=
  λ (x y : NonnegativeRationals),
  match (isdecrel_leNonnegativeRationals x y) with
  | ii1 _ => y
  | ii2 _ => x
  end.
Lemma NQmax_eq_zero :
  ∀ x y : NonnegativeRationals, NQmax x y = 0 -> (x = 0) × (y = 0).
Proof.
  intros x y.
  unfold NQmax.
  destruct isdecrel_leNonnegativeRationals as [Hle | Hlt] ; intro H ; split.
  - rewrite NonnegativeRationals_eq0_le0.
    apply istrans_leNonnegativeRationals with (1 := Hle).
    now rewrite <- NonnegativeRationals_eq0_le0.
  - exact H.
  - exact H.
  - rewrite NonnegativeRationals_eq0_le0, <- H.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma NQmax_case :
  ∀ (P : NonnegativeRationals -> UU),
  ∀ x y : NonnegativeRationals, P x -> P y -> P (NQmax x y).
Proof.
  intros P x y Hx Hy.
  unfold NQmax.
  now destruct isdecrel_leNonnegativeRationals.
Qed.
Lemma NQmax_case_strong :
  ∀ (P : NonnegativeRationals -> UU),
  ∀ x y : NonnegativeRationals, (y <= x -> P x) -> (x <= y -> P y) -> P (NQmax x y).
Proof.
  intros P x y Hx Hy.
  unfold NQmax.
  destruct isdecrel_leNonnegativeRationals as [Hle | Hlt].
  - now apply Hy.
  - apply Hx.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma iscomm_NQmax :
  ∀ x y, NQmax x y = NQmax y x.
Proof.
  intros x y.
  apply NQmax_case_strong ; intro Hle ;
  apply NQmax_case_strong ; intro Hle'.
  - now apply isantisymm_leNonnegativeRationals.
  - reflexivity.
  - reflexivity.
  - now apply isantisymm_leNonnegativeRationals.
Qed.
Lemma NQmax_le_l :
  ∀ x y : NonnegativeRationals, x <= NQmax x y.
Proof.
  intros x y.
  unfold NQmax.
  destruct isdecrel_leNonnegativeRationals as [Hle | Hlt].
  - exact Hle.
  - apply isrefl_leNonnegativeRationals.
Qed.
Lemma NQmax_le_r :
  ∀ x y : NonnegativeRationals, y <= NQmax x y.
Proof.
  intros x y.
  rewrite iscomm_NQmax.
  now apply NQmax_le_l.
Qed.

Close Scope NRat_scope.

(** ** Opacify *)

Global Opaque NonnegativeRationals NonnegativeRationals_EffectivelyOrderedSet.

(* End of the file hnnq.v *)
