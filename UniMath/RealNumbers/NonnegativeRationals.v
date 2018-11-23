(** Catherine Lelay. Sep. 2015 *)

Unset Kernel Term Sharing.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Sets.

Require Import UniMath.RealNumbers.Sets.
Require Import UniMath.RealNumbers.Fields.
Require Export UniMath.Algebra.DivisionRig.
Require Import UniMath.RealNumbers.Prelim.

Opaque hq.

Local Open Scope hq_scope.

(** * Definition of non-negative rational numbers *)

Definition hnnq_set := subset (hqleh 0).

Local Definition hnnq_set_to_hq (r : hnnq_set) : hq := pr1 r.

Local Definition hq_to_hnnq_set (r : hq) (Hr : hqleh 0 r) : hnnq_set :=
  r ,, Hr.

Local Definition hnnq_zero: hnnq_set := hq_to_hnnq_set 0 (isreflhqleh 0).
Local Definition hnnq_one: hnnq_set := hq_to_hnnq_set 1 (hqlthtoleh 0 1 hq1_gt0).
Local Definition hnnq_plus: binop hnnq_set :=
  λ x y : hnnq_set, hq_to_hnnq_set (pr1 x + pr1 y) (hq0lehandplus _ _ (pr2 x) (pr2 y)).
Local Definition hnnq_minus: binop hnnq_set.
Proof.
  intros x y.
  induction (hqgthorleh (pr1 x) (pr1 y)) as [H | _].
  exact (hq_to_hnnq_set (pr1 x - pr1 y) (hq0leminus _ _ (hqlthtoleh _ _ H))).
  exact hnnq_zero.
Defined.
Local Definition hnnq_mult: binop hnnq_set :=
  λ x y : hnnq_set, hq_to_hnnq_set (pr1 x * pr1 y) (hqmultgeh0geh0 (pr2 x) (pr2 y)).
Local Definition hnnq_inv: unop hnnq_set.
Proof.
  intros x.
  induction (hqlehchoice 0 (pr1 x) (pr2 x)) as [Hx0 | _].
  exact (hq_to_hnnq_set (/ pr1 x) (hqlthtoleh 0 (/ pr1 x) (hqinv_gt0 (pr1 x) Hx0))).
  exact x.
Defined.
Local Definition hnnq_div : binop hnnq_set := λ x y : hnnq_set, hnnq_mult x (hnnq_inv y).

(** ** Equality and order on non-negative rational numbers *)

Local Definition hnnq_le : hrel hnnq_set := resrel hqleh (hqleh 0).
Local Lemma ispreorder_hnnq_le : ispreorder hnnq_le.
Proof.
  split.
 intros x y z.
  now apply istranshqleh.
  intros x.
  now apply isreflhqleh.
Qed.

Local Definition hnnq_ge : hrel hnnq_set := resrel hqgeh (hqleh 0).
Local Lemma ispreorder_hnnq_ge : ispreorder hnnq_ge.
Proof.
  set (H := ispreorder_hnnq_le).
  split.
  intros x y z Hxy Hyz.
  now apply (pr1 H) with y.
  intros x.
  now apply (pr2 H).
Qed.

Local Definition hnnq_lt : hrel hnnq_set := resrel hqlth (hqleh 0).
Local Lemma isStrongOrder_hnnq_lt : isStrongOrder hnnq_lt.
Proof.
  repeat split.
  - intros x y z.
    now apply istranshqlth.
  - intros x y z Hxz.
    generalize (hqlthorgeh (pr1 x) (pr1 y)) ; apply sumofmaps ; intros Hxy.
    apply hinhpr ; left.
    exact Hxy.
    apply hinhpr ; right.
    apply hqlehlthtrans with (pr1 x).
    exact Hxy.
    exact Hxz.
  - intros x.
    now apply isirreflhqlth.
Qed.

Local Definition hnnq_gt : hrel hnnq_set := resrel hqgth (hqleh 0).
Local Lemma isStrongOrder_hnnq_gt : isStrongOrder hnnq_gt.
Proof.
  set (H := isStrongOrder_reverse _ isStrongOrder_hnnq_lt).
  repeat split.
  intros x y z.
  now apply (pr1 H).
  intros x y z.
  now apply (pr1 (pr2 H)).
  intros x.
  now apply (pr2 (pr2 H)).
Qed.

Local Lemma isEffectiveOrder_hnnq : isEffectiveOrder hnnq_le hnnq_lt.
Proof.
  split ; [ split | repeat split ].
  - exact ispreorder_hnnq_le.
  - exact isStrongOrder_hnnq_lt.
  - intros. assumption.
  - intros. assumption.
  - intros x y z.
    now apply hqlthlehtrans.
  - intros x y z.
    now apply hqlehlthtrans.
Qed.

(** ** hnnq is a half field *)

Local Lemma iscomm_hnnq_plus:
  iscomm hnnq_plus.
Proof.
  intros x y.
  apply subtypeEquality_prop.
  now apply hqpluscomm.
Qed.
Local Lemma isassoc_hnnq_plus :
  isassoc hnnq_plus.
Proof.
  intros x y z.
  apply subtypeEquality_prop.
  now apply hqplusassoc.
Qed.
Local Lemma islunit_hnnq_zero_plus:
  islunit hnnq_plus hnnq_zero.
Proof.
  intros x.
  apply subtypeEquality_prop.
  now apply hqplusl0.
Qed.
Local Lemma isrunit_hnnq_zero_plus:
  isrunit hnnq_plus hnnq_zero.
Proof.
  intros x.
  rewrite iscomm_hnnq_plus.
  now apply islunit_hnnq_zero_plus.
Qed.
Local Lemma iscomm_hnnq_mult:
  iscomm hnnq_mult.
Proof.
  intros x y.
  apply subtypeEquality_prop.
  now apply hqmultcomm.
Qed.
Local Lemma isassoc_hnnq_mult:
  isassoc hnnq_mult.
Proof.
  intros x y z.
  apply subtypeEquality_prop.
  now apply hqmultassoc.
Qed.
Local Lemma islunit_hnnq_one_mult:
  islunit hnnq_mult hnnq_one.
Proof.
  intros x.
  apply subtypeEquality_prop.
  now apply hqmultl1.
Qed.
Local Lemma isrunit_hnnq_one_mult:
  isrunit hnnq_mult hnnq_one.
Proof.
  intros x.
  rewrite iscomm_hnnq_mult.
  now apply islunit_hnnq_one_mult.
Qed.
Local Lemma islinv'_hnnq_inv:
  islinv' hnnq_one hnnq_mult (hnnq_lt hnnq_zero)
          (λ x : subset (hnnq_lt hnnq_zero), hnnq_inv (pr1 x)).
Proof.
  intros x Hx0.
  unfold hnnq_inv.
  change (hqlehchoice 0 (pr1 (pr1 (x,, Hx0))) (pr2 (pr1 (x,, Hx0)))) with (hqlehchoice 0 (pr1 x) (pr2 x)).
  generalize (hqlehchoice 0 (pr1 x) (pr2 x)).
  apply coprod_rect ; intros Hx0'.
  - apply subtypeEquality_prop.
    apply hqislinvmultinv.
    now apply (hqgth_hqneq (pr1 x) 0), Hx0'.
  - apply fromempty.
    generalize (pathsinv0 Hx0').
    apply hqgth_hqneq, Hx0.
Qed.
Local Lemma isrinv'_hnnq_inv:
 isrinv' hnnq_one hnnq_mult (hnnq_lt hnnq_zero)
         (λ x : subset (hnnq_lt hnnq_zero), hnnq_inv (pr1 x)).
Proof.
  intros x Hx.
  rewrite iscomm_hnnq_mult.
  now apply islinv'_hnnq_inv.
Qed.
Local Lemma isldistr_hnnq_plus_mult:
  isldistr hnnq_plus hnnq_mult.
Proof.
  intros x y z.
  apply subtypeEquality_prop.
  now apply hqldistr.
Qed.
Local Lemma isrdistr_hnnq_plus_mult:
  isrdistr hnnq_plus hnnq_mult.
Proof.
  intros x y z.
  rewrite !(iscomm_hnnq_mult _ z).
  now apply isldistr_hnnq_plus_mult.
Qed.

Local Definition isabmonoidop_hnnq_plus: isabmonoidop hnnq_plus.
Proof.
  repeat split.
  - exact isassoc_hnnq_plus.
  - exists hnnq_zero ; split.
    + exact islunit_hnnq_zero_plus.
    + exact isrunit_hnnq_zero_plus.
  - exact iscomm_hnnq_plus.
Defined.
Local Definition ismonoidop_hnnq_mult : ismonoidop hnnq_mult.
Proof.
  split.
  - exact isassoc_hnnq_mult.
  - exists hnnq_one ; split.
    + exact islunit_hnnq_one_mult.
    + exact isrunit_hnnq_one_mult.
Defined.
Local Definition commrig_hnnq: commrig.
Proof.
  exists (hnnq_set,,hnnq_plus,,hnnq_mult).
  repeat split.
  - exists (isabmonoidop_hnnq_plus,,ismonoidop_hnnq_mult) ; split.
    + intro x.
      apply subtypeEquality_prop.
      apply hqmult0x.
    + intro x.
      apply subtypeEquality_prop.
      apply hqmultx0.
  - exact isldistr_hnnq_plus_mult.
  - exact isrdistr_hnnq_plus_mult.
  - exact iscomm_hnnq_mult.
Defined.
Local Definition CommDivRig_hnnq: CommDivRig.
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
Definition NonnegativeRationals_to_Rationals : NonnegativeRationals → hq :=
  pr1.
Definition Rationals_to_NonnegativeRationals (r : hq) (Hr : hqleh 0%hq r) : NonnegativeRationals :=
  tpair _ r Hr.

Delimit Scope NRat_scope with NRat.

(** ** Definitions *)

Definition NonnegativeRationals_EffectivelyOrderedSet :=
  @pairEffectivelyOrderedSet NonnegativeRationals (pairEffectiveOrder _ _ isEffectiveOrder_hnnq).

Definition leNonnegativeRationals : po NonnegativeRationals :=
  EOle (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition geNonnegativeRationals : po NonnegativeRationals :=
  EOge (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition ltNonnegativeRationals : StrongOrder NonnegativeRationals :=
  EOlt (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition gtNonnegativeRationals : StrongOrder NonnegativeRationals :=
  EOgt (X := NonnegativeRationals_EffectivelyOrderedSet).

Notation "x <= y" := (EOle_rel (X := NonnegativeRationals_EffectivelyOrderedSet) x y) (at level 70, no associativity) : NRat_scope.
Notation "x >= y" := (EOge_rel (X := NonnegativeRationals_EffectivelyOrderedSet) x y) (at level 70, no associativity) : NRat_scope.
Notation "x < y" := (EOlt_rel (X := NonnegativeRationals_EffectivelyOrderedSet) x y) (at level 70, no associativity) : NRat_scope.
Notation "x > y" := (EOgt_rel (X := NonnegativeRationals_EffectivelyOrderedSet) x y) (at level 70, no associativity) : NRat_scope.

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

Definition nat_to_NonnegativeRationals (n : nat) : NonnegativeRationals :=
  Rationals_to_NonnegativeRationals (hztohq (nattohz n)) (hztohqandleh 0%hz _ (nattohzandleh O n (natleh0n n))).

Notation "0" := zeroNonnegativeRationals : NRat_scope.
Notation "1" := oneNonnegativeRationals : NRat_scope.
Notation "2" := twoNonnegativeRationals : NRat_scope.

Notation "x + y" := (plusNonnegativeRationals x y) (at level 50, left associativity) : NRat_scope.
Notation "x - y" := (minusNonnegativeRationals x y) (at level 50, left associativity) : NRat_scope.
Notation "x * y" := (multNonnegativeRationals x y) (at level 40, left associativity) : NRat_scope.
Notation "/ x" := (invNonnegativeRationals x) (at level 35, right associativity) : NRat_scope.
Notation "x / y" := (divNonnegativeRationals x y) (at level 40, left associativity) : NRat_scope.

Local Open Scope NRat_scope.

(** *** Correctness of definitions *)

Lemma zeroNonnegativeRationals_correct :
  0 = Rationals_to_NonnegativeRationals 0%hq (isreflhqleh 0%hq).
Proof.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma oneNonnegativeRationals_correct :
  1 = Rationals_to_NonnegativeRationals 1%hq hq1ge0.
Proof.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma twoNonnegativeRationals_correct :
  2 = Rationals_to_NonnegativeRationals 2%hq (hqlthtoleh _ _ hq2_gt0).
Proof.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma plusNonnegativeRationals_correct :
  ∏ (x y : NonnegativeRationals),
    x + y = Rationals_to_NonnegativeRationals (pr1 x + pr1 y)%hq (hq0lehandplus _ _ (pr2 x) (pr2 y)).
Proof.
  intros x y.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma minusNonnegativeRationals_correct :
  ∏ (x y : NonnegativeRationals) (Hminus : y <= x),
    x - y = Rationals_to_NonnegativeRationals (pr1 x - pr1 y)%hq (hq0leminus _ _ Hminus).
Proof.
  intros x y H.
  apply subtypeEquality_prop.
  unfold minusNonnegativeRationals, hnnq_minus.
  generalize (hqgthorleh (pr1 x) (pr1 y)).
  apply coprod_rect ; [intros Hgt | intros Hle].
  - reflexivity.
  - generalize (isantisymmhqleh _ _ Hle H) ; intros Heq.
    rewrite coprod_rect_compute_2.
    generalize (hq0leminus (pr1 y) (pr1 x) H).
    rewrite Heq, hqrminus.
    intros H0.
    reflexivity.
Qed.
Lemma multNonnegativeRationals_correct :
  ∏ (x y : NonnegativeRationals),
    x * y = Rationals_to_NonnegativeRationals (pr1 x * pr1 y)%hq ( hq0lehandmult _ _ (pr2 x) (pr2 y)).
Proof.
  intros x y.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma invNonnegativeRationals_correct :
  ∏ (x : NonnegativeRationals) (Hx : 0 < x),
    / x = Rationals_to_NonnegativeRationals (/ pr1 x)%hq (hqlthtoleh _ _ (hqinv_gt0 _ Hx)).
Proof.
  intros x Hx0.
  apply subtypeEquality_prop.
  unfold invNonnegativeRationals, hnnq_inv.
  generalize (hqlehchoice 0%hq (pr1 x) (pr2 x)).
  apply coprod_rect ; [intros Hlt | intros Heq].
  - reflexivity.
  - apply fromempty ; generalize Hx0.
    change x with (pr1 x,,pr2 x).
    generalize (pr2 x).
    rewrite <- Heq ; intro.
    exact (isirreflhqlth 0%hq).
Qed.

Lemma leNonnegativeRationals_correct :
  ∏ x y : NonnegativeRationals, (x <= y) = (pr1 x <= pr1 y)%hq.
Proof.
  intros x y.
  reflexivity.
Qed.
Lemma geNonnegativeRationals_correct :
  ∏ x y : NonnegativeRationals, (x >= y) = (pr1 x >= pr1 y)%hq.
Proof.
  intros x y.
  reflexivity.
Qed.
Lemma ltNonnegativeRationals_correct :
  ∏ x y : NonnegativeRationals, (x < y) = (pr1 x < pr1 y)%hq.
Proof.
  intros x y.
  reflexivity.
Qed.
Lemma gtNonnegativeRationals_correct :
  ∏ x y : NonnegativeRationals, (x > y) = (pr1 x > pr1 y)%hq.
Proof.
  intros x y.
  reflexivity.
Qed.

(** ** Theorems about order *)

(** *** Decidability *)

Lemma isdeceq_NonnegativeRationals :
  ∏ x y : NonnegativeRationals, (x = y) ⨿ (x != y).
Proof.
  intros x y.
  generalize (isdeceqhq (pr1 x) (pr1 y)) ;
  apply sumofmaps ; intros H.
  - left.
    apply subtypeEquality_prop.
    exact H.
  - right.
    intros H0 ; apply H.
    revert H0.
    apply base_paths.
Qed.
Lemma isdecrel_leNonnegativeRationals :
  ∏ x y : NonnegativeRationals, (x <= y) ⨿ ¬ (x <= y).
Proof.
  intros x y.
  apply isdecrelhqleh.
Qed.
Lemma isdecrel_ltNonnegativeRationals :
  ∏ x y : NonnegativeRationals, (x < y) ⨿ ¬ (x < y).
Proof.
  intros x y.
  apply isdecrelhqlth.
Qed.

Lemma le_eqorltNonnegativeRationals :
  ∏ x y : NonnegativeRationals, x <= y -> (x = y) ⨿ (x < y).
Proof.
  intros x y Hle.
  generalize (hqlehchoice (pr1 x) (pr1 y) Hle) ;
    apply sumofmaps ; [intros Hlt | intros Heq].
  - right ; exact Hlt.
  - left.
    now apply subtypeEquality_prop, Heq.
Qed.
Lemma noteq_ltorgtNonnegativeRationals :
  ∏ x y : NonnegativeRationals, x != y -> (x < y) ⨿ (x > y).
Proof.
  intros x y Hneq.
  generalize (isdecrel_leNonnegativeRationals x y) ;
    apply sumofmaps ; [intros Hle|intros Hlt].
  - left.
    apply le_eqorltNonnegativeRationals in Hle.
    revert Hle ; apply sumofmaps ; [intros Heq | intros Hlt].
    + now apply fromempty, Hneq, Heq.
    + exact Hlt.
  - right.
    apply neghqgehtolth.
    exact Hlt.
Qed.
Lemma eq0orgt0NonnegativeRationals :
  ∏ x : NonnegativeRationals, (x = 0) ⨿ (0 < x).
Proof.
  intros x.
  generalize (le_eqorltNonnegativeRationals 0 x (pr2 x)) ; apply sumofmaps ; intros Hx.
  rewrite Hx ; now left.
  right ; exact Hx.
Qed.

(** *** Basic theorems about order *)

Definition lt_leNonnegativeRationals :
  ∏ x y : NonnegativeRationals, x < y -> x <= y
  := EOlt_le (X := NonnegativeRationals_EffectivelyOrderedSet).

Definition isrefl_leNonnegativeRationals:
  ∏ x : NonnegativeRationals, x <= x :=
  isrefl_EOle (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition istrans_leNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, x <= y -> y <= z -> x <= z :=
  istrans_EOle (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition isirrefl_ltNonnegativeRationals:
  ∏ x : NonnegativeRationals, ¬ (x < x) :=
  isirrefl_EOlt (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition istrans_ltNonnegativeRationals :
  ∏ x y z : NonnegativeRationals, x < y -> y < z -> x < z
  := istrans_EOlt (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition istrans_lt_le_ltNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, x < y -> y <= z -> x < z
  := istrans_EOlt_le (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition istrans_le_lt_ltNonnegativeRationals :
  ∏ x y z : NonnegativeRationals, x <= y -> y < z -> x < z
  := istrans_EOle_lt (X := NonnegativeRationals_EffectivelyOrderedSet).

Lemma isantisymm_leNonnegativeRationals :
  ∏ x y : NonnegativeRationals, x <= y -> y <= x -> x = y.
Proof.
  intros x y Hle Hge.
  apply subtypeEquality_prop.
  now apply isantisymmhqleh.
Qed.

Definition ge_leNonnegativeRationals:
  ∏ x y : NonnegativeRationals, (x >= y) <-> (y <= x)
  := EOge_le (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition lt_gtNonnegativeRationals:
  ∏ x y : NonnegativeRationals, (x > y) <-> (y < x)
  := EOgt_lt (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition notlt_geNonnegativeRationals:
  ∏ x y : NonnegativeRationals, (¬ (x < y)) <-> (y <= x)
  := not_EOlt_le (X := NonnegativeRationals_EffectivelyOrderedSet).
Lemma notge_ltNonnegativeRationals :
  ∏ x y : NonnegativeRationals, (¬ (y <= x)) <-> (x < y).
Proof.
  intros x y.
  split.
  - now apply neghqgehtolth.
  - now apply hqlthtoneghqgeh.
Qed.

Definition ltNonnegativeRationals_noteq :
  ∏ x y, x < y -> x != y
  := EOlt_noteq (X := NonnegativeRationals_EffectivelyOrderedSet).
Definition gtNonnegativeRationals_noteq :
  ∏ x y, x > y -> x != y
  := EOgt_noteq (X := NonnegativeRationals_EffectivelyOrderedSet).

Lemma between_ltNonnegativeRationals :
  ∏ x y : NonnegativeRationals,
    x < y -> ∑ t : NonnegativeRationals, x < t × t < y.
Proof.
  intros x y H.
  set (z := hqlth_between (pr1 x) (pr1 y) H).
  assert (Hz : hqleh 0%hq (pr1 z)).
  { apply istranshqleh with (pr1 x).
    now apply (pr2 x).
    apply (hqlthtoleh (pr1 x) (pr1 z)), (pr1 (pr2 z)). }
  exists (hq_to_hnnq_set _ Hz).
  exact (pr2 z).
Qed.

(** *** Order and 0 *)

Lemma isnonnegative_NonnegativeRationals :
  ∏ x : NonnegativeRationals , 0 <= x.
Proof.
  intros x.
  apply (pr2 x).
Qed.
Lemma isnonnegative_NonnegativeRationals' :
  ∏ x : NonnegativeRationals , ¬ (x < 0).
Proof.
  intros x.
  apply (pr2 x).
Qed.

Lemma NonnegativeRationals_eq0_le0 :
  ∏ r : NonnegativeRationals, (r <= 0) -> (r = 0).
Proof.
  intros r Hr0.
  apply subtypeEquality_prop.
  apply isantisymmhqleh.
  apply Hr0.
  apply (pr2 r).
Qed.
Lemma NonnegativeRationals_neq0_gt0 :
  ∏ r : NonnegativeRationals, (r != 0) -> (0 < r).
Proof.
  intros r Hr0.
  apply neghqlehtogth.
  intro H ; apply Hr0.
  now apply NonnegativeRationals_eq0_le0.
Qed.

Lemma ispositive_oneNonnegativeRationals : 0 < 1.
Proof.
  exact hq1_gt0.
Qed.
Lemma ispositive_twoNonnegativeRationals : 0 < 2.
Proof.
  exact hq2_gt0.
Qed.
Lemma one_lt_twoNonnegativeRationals : 1 < 2.
Proof.
  change (1 < 2)%hq.
  rewrite <- (hqplusr0 1%hq), hq2eq1plus1.
  apply hqlthandplusl.
  exact hq1_gt0.
Qed.

(** ** Theorems about algebra *)
(** *** Addition *)
(** Rewritings *)

Definition isassoc_plusNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, x + y + z = x + (y + z) :=
  CommDivRig_isassoc_plus.

Definition islunit_zeroNonnegativeRationals:
  ∏ r : NonnegativeRationals, 0 + r = r :=
  CommDivRig_islunit_zero.

Definition isrunit_zeroNonnegativeRationals:
  ∏ r : NonnegativeRationals, r + 0 = r :=
  CommDivRig_isrunit_zero.

Definition iscomm_plusNonnegativeRationals:
  ∏ x y : NonnegativeRationals, x + y = y + x :=
  CommDivRig_iscomm_plus.

(** Order *)

Lemma plusNonnegativeRationals_ltcompat_r :
  ∏ x y z : NonnegativeRationals, (y < z) <-> (y + x < z + x).
Proof.
  intros x y z.
  split.
  now apply hqlthandplusr.
  now apply hqlthandplusrinv.
Qed.
Lemma plusNonnegativeRationals_ltcompat_l :
  ∏ x y z : NonnegativeRationals, (y < z) <-> (x + y < x + z).
Proof.
  intros x y z.
  rewrite !(iscomm_plusNonnegativeRationals x).
  now apply plusNonnegativeRationals_ltcompat_r.
Qed.

Lemma plusNonnegativeRationals_lecompat_r :
  ∏ r q n : NonnegativeRationals, (q <= n) <-> (q + r <= n + r).
Proof.
  intros r q n.
  split.
  - now apply hqlehandplusr.
  - now apply hqlehandplusrinv.
Qed.
Lemma plusNonnegativeRationals_lecompat_l :
  ∏ r q n : NonnegativeRationals, (q <= n) <-> (r + q <= r + n).
Proof.
  intros r q n.
  rewrite ! (iscomm_plusNonnegativeRationals r).
  now apply plusNonnegativeRationals_lecompat_r.
Qed.

Lemma plusNonnegativeRationals_eqcompat_l:
  ∏ k x y : NonnegativeRationals,
    (k + x = k + y) -> (x = y).
Proof.
  intros k x y H.
  apply isantisymm_leNonnegativeRationals ;
    apply_pr2 (plusNonnegativeRationals_lecompat_l k) ;
    rewrite H ;
    apply isrefl_leNonnegativeRationals.
Qed.
Lemma plusNonnegativeRationals_eqcompat_r:
  ∏ k x y : NonnegativeRationals,
    (x + k = y + k) -> (x = y).
Proof.
  intros k x y.
  rewrite !(iscomm_plusNonnegativeRationals _ k).
  now apply plusNonnegativeRationals_eqcompat_l.
Qed.

Lemma plusNonnegativeRationals_ltcompat :
  ∏ x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x + y < x' + y'.
Proof.
  intros x x' y y' Hx Hy.
  apply istrans_ltNonnegativeRationals with (x + y').
  now apply hqlthandplusl, Hy.
  now apply hqlthandplusr, Hx.
Qed.
Lemma plusNonnegativeRationals_le_lt_ltcompat :
  ∏ x x' y y' : NonnegativeRationals,
    x <= x' -> y < y' -> x + y < x' + y'.
Proof.
  intros x x' y y' Hx Hy.
  apply istrans_lt_le_ltNonnegativeRationals with (x + y').
  now apply hqlthandplusl, Hy.
  now apply hqlehandplusr, Hx.
Qed.
Lemma plusNonnegativeRationals_lt_le_ltcompat :
  ∏ x x' y y' : NonnegativeRationals,
    x < x' -> y <= y' -> x + y < x' + y'.
Proof.
  intros x x' y y' Hx Hy.
  apply istrans_le_lt_ltNonnegativeRationals with (x + y').
  now apply hqlehandplusl, Hy.
  now apply hqlthandplusr, Hx.
Qed.

Lemma plusNonnegativeRationals_le_r :
  ∏ r q : NonnegativeRationals, r <= r + q.
Proof.
  intros r q.
  pattern r at 1.
  rewrite <- (isrunit_zeroNonnegativeRationals r).
  apply hqlehandplusl.
  apply (pr2 q).
Qed.
Lemma plusNonnegativeRationals_le_l :
  ∏ r q : NonnegativeRationals, r <= q + r.
Proof.
  intros r q.
  rewrite iscomm_plusNonnegativeRationals.
  now apply plusNonnegativeRationals_le_r.
Qed.

Lemma ispositive_plusNonnegativeRationals_l :
  ∏ x y : NonnegativeRationals, 0 < x -> 0 < x + y.
Proof.
  intros x y Hx.
  apply istrans_lt_le_ltNonnegativeRationals with x.
  exact Hx.
  now apply plusNonnegativeRationals_le_r.
Qed.
Lemma ispositive_plusNonnegativeRationals_r :
  ∏ x y : NonnegativeRationals, 0 < y -> 0 < x + y.
Proof.
  intros x y Hy.
  apply istrans_lt_le_ltNonnegativeRationals with y.
  exact Hy.
  now apply plusNonnegativeRationals_le_l.
Qed.

Lemma plusNonnegativeRationals_lt_r :
  ∏ r q : NonnegativeRationals, 0 < q -> r < r + q.
Proof.
  intros x y Hy0.
  pattern x at 1.
  rewrite <- (isrunit_zeroNonnegativeRationals x).
  apply plusNonnegativeRationals_ltcompat_l.
  exact Hy0.
Qed.
Lemma plusNonnegativeRationals_lt_l :
  ∏ r q : NonnegativeRationals, 0 < r -> q < r + q.
Proof.
  intros x y.
  rewrite iscomm_plusNonnegativeRationals.
  now apply plusNonnegativeRationals_lt_r.
Qed.

(** *** Substraction *)
(** Rewriting *)

Lemma minusNonnegativeRationals_eq_zero:
  ∏ x y : NonnegativeRationals, x <= y -> x - y = 0.
Proof.
  intros x y Hle.
  unfold minusNonnegativeRationals, hnnq_minus.
  generalize (hqgthorleh (pr1 x) (pr1 y)).
  apply coprod_rect ; intros H.
  - apply fromempty.
    exact (Hle H).
  - reflexivity.
Qed.
Lemma minusNonnegativeRationals_plus_r :
  ∏ r q : NonnegativeRationals,
    r <= q -> (q - r) + r = q.
Proof.
  intros r q H.
  unfold minusNonnegativeRationals, hnnq_minus.
  generalize (hqgthorleh (pr1 q) (pr1 r)).
  apply coprod_rect ; intros H'.
  - rewrite coprod_rect_compute_1.
    apply subtypeEquality_prop.
    unfold hqminus.
    pattern r at 4.
    simpl.
    generalize (pr1 r) (pr1 q) (pr2 r) (hq0leminus (pr1 r) (pr1 q) (hqlthtoleh (pr1 r) (pr1 q) H')) ; intros r' q' Hr Hrq.
    now rewrite hqplusassoc, hqlminus, hqplusr0.
  - rewrite coprod_rect_compute_2.
    apply subtypeEquality_prop.
    generalize (isantisymmhqleh _ _ H H').
    simpl.
    generalize (pr1 r) (pr2 r) (pr1 q) ; intros r' Hr' q' Heq.
    now rewrite hqplusl0.
Qed.

Lemma plusNonnegativeRationals_minus_r :
  ∏ q r : NonnegativeRationals, (r + q) - q = r.
Proof.
  intros q r.
  change r with (pr1 r,,pr2 r).
  generalize (pr1 r) (pr2 r) (pr1 q) (pr2 q) ; intros r' Hr q' Hq.
  rewrite (minusNonnegativeRationals_correct _ _ (plusNonnegativeRationals_le_l _ _)).
  apply subtypeEquality_prop.
  simpl pr1.
  unfold hqminus.
  rewrite hqplusassoc.
  rewrite (hqpluscomm (pr1 q)).
  rewrite hqlminus.
  rewrite hqplusr0.
  reflexivity.
Qed.

Lemma plusNonnegativeRationals_minus_l :
  ∏ q r : NonnegativeRationals, (q + r) - q = r.
Proof.
  intros q r.
  rewrite iscomm_plusNonnegativeRationals.
  now apply plusNonnegativeRationals_minus_r.
Qed.

Lemma minusNonnegativeRationals_correct_l :
  ∏ x y z : NonnegativeRationals, x = y + z -> z = x - y.
Proof.
  intros x y z ->.
  now rewrite plusNonnegativeRationals_minus_l.
Qed.
Lemma minusNonnegativeRationals_correct_r :
  ∏ x y z : NonnegativeRationals, x = y + z -> y = x - z.
Proof.
  intros x y z ->.
  now rewrite plusNonnegativeRationals_minus_r.
Qed.

Lemma minusNonnegativeRationals_zero_l :
  ∏ x : NonnegativeRationals, 0 - x = 0.
Proof.
  intros x.
  apply minusNonnegativeRationals_eq_zero.
  now apply isnonnegative_NonnegativeRationals.
Qed.
Lemma minusNonnegativeRationals_zero_r :
  ∏ x : NonnegativeRationals, x - 0 = x.
Proof.
  intros x.
  rewrite <- (isrunit_zeroNonnegativeRationals (x - 0)).
  apply minusNonnegativeRationals_plus_r.
  now apply isnonnegative_NonnegativeRationals.
Qed.

Lemma minusNonnegativeRationals_plus_exchange :
  ∏ x y z : NonnegativeRationals, y <= x -> x - y + z = (x + z) - y.
Proof.
  intros x y z Hxy.
  assert (Hxzy : y <= x + z).
  { apply istrans_leNonnegativeRationals with x.
    exact Hxy.
    apply plusNonnegativeRationals_le_r. }
  rewrite (minusNonnegativeRationals_correct _ _ Hxy), (minusNonnegativeRationals_correct _ _ Hxzy).
  revert Hxy Hxzy.
  intros.
  apply subtypeEquality_prop.
  change (pr1 x - pr1 y + pr1 z = (pr1 x + pr1 z) - pr1 y)%hq.
  now unfold hqminus ; rewrite !hqplusassoc, (hqpluscomm (pr1 z)).
Qed.

(** Order *)

Lemma ispositive_minusNonnegativeRationals :
  ∏ x y : NonnegativeRationals, (x < y) <-> (0 < y - x).
Proof.
  intros x y.
  split ; intro Hlt.
  - apply_pr2 (plusNonnegativeRationals_ltcompat_r x).
    rewrite islunit_zeroNonnegativeRationals, minusNonnegativeRationals_plus_r.
    + exact Hlt.
    + now apply lt_leNonnegativeRationals, Hlt.
  - revert Hlt.
    unfold minusNonnegativeRationals, hnnq_minus.
    generalize (hqgthorleh (pr1 y) (pr1 x)).
    apply (coprod_rect (λ _, _ → _)) ; intros H0 ; intro Hlt.
    + exact H0.
    + now apply isirrefl_ltNonnegativeRationals in Hlt.
Qed.

Lemma minusNonnegativeRationals_le :
  ∏ x y : NonnegativeRationals, x - y <= x.
Proof.
  intros x y.
  apply_pr2 (plusNonnegativeRationals_lecompat_r y).
  generalize (isdecrel_leNonnegativeRationals y x) ;
    apply sumofmaps ; [intros Hle | intros Hlt].
  - rewrite minusNonnegativeRationals_plus_r.
    now apply plusNonnegativeRationals_le_r.
    exact Hle.
  - rewrite minusNonnegativeRationals_eq_zero.
    rewrite islunit_zeroNonnegativeRationals.
    apply plusNonnegativeRationals_le_l.
    apply lt_leNonnegativeRationals.
    now apply notge_ltNonnegativeRationals.
Qed.

Lemma minusNonnegativeRationals_lecompat_l :
  ∏ k x y : NonnegativeRationals, x <= y -> x - k <= y - k.
Proof.
  intros k x y Hxy.
  generalize (isdecrel_leNonnegativeRationals k x) ;
    apply sumofmaps ; intros Hkx.
  - apply_pr2 (plusNonnegativeRationals_lecompat_r k).
    rewrite !minusNonnegativeRationals_plus_r.
    exact Hxy.
    now apply istrans_leNonnegativeRationals with (2 := Hxy).
    exact Hkx.
  - rewrite minusNonnegativeRationals_eq_zero.
    now apply isnonnegative_NonnegativeRationals.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma minusNonnegativeRationals_lecompat_l' :
  ∏ k x y : NonnegativeRationals, k <= y -> x - k <= y - k -> x <= y.
Proof.
  intros k x y Hky H.
  generalize (isdecrel_leNonnegativeRationals k x) ;
    apply sumofmaps ; intros Hkx.
  - rewrite <- (minusNonnegativeRationals_plus_r _ _ Hkx), <- (minusNonnegativeRationals_plus_r _ _ Hky).
    apply plusNonnegativeRationals_lecompat_r.
    exact H.
  - apply istrans_leNonnegativeRationals with k.
    apply lt_leNonnegativeRationals.
    now apply notge_ltNonnegativeRationals.
    exact Hky.
Qed.

Lemma minusNonnegativeRationals_lecompat_r :
  ∏ k x y : NonnegativeRationals, x <= y -> k - y <= k - x.
Proof.
  intros k x y Hxy.
  generalize (isdecrel_leNonnegativeRationals y k) ;
    apply sumofmaps ; intros Hky.
  - apply_pr2 (plusNonnegativeRationals_lecompat_r y).
    rewrite minusNonnegativeRationals_plus_r, minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals, <- minusNonnegativeRationals_plus_exchange.
    apply plusNonnegativeRationals_le_l.
    exact Hxy.
    apply istrans_leNonnegativeRationals with y.
    exact Hxy.
    exact Hky.
    exact Hky.
  - rewrite minusNonnegativeRationals_eq_zero.
    now apply isnonnegative_NonnegativeRationals.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma minusNonnegativeRationals_lecompat_r' :
  ∏ k x y : NonnegativeRationals, x <= k -> k - y <= k - x -> x <= y.
Proof.
  intros k x y Hkx H.
  generalize (isdecrel_leNonnegativeRationals y k) ;
    apply sumofmaps ; intros Hky.
  - apply (plusNonnegativeRationals_lecompat_r y) in H.
    rewrite minusNonnegativeRationals_plus_r, iscomm_plusNonnegativeRationals in H.
    apply (plusNonnegativeRationals_lecompat_r x) in H ; rewrite isassoc_plusNonnegativeRationals, minusNonnegativeRationals_plus_r, iscomm_plusNonnegativeRationals in H.
    now apply_pr2 (plusNonnegativeRationals_lecompat_r k).
    exact Hkx.
    exact Hky.
  - apply istrans_leNonnegativeRationals with k.
    exact Hkx.
    apply lt_leNonnegativeRationals.
    now apply notge_ltNonnegativeRationals.
Qed.

Lemma minusNonnegativeRationals_ltcompat_l:
  ∏ x y z : NonnegativeRationals, x < y -> z < y -> x - z < y - z.
Proof.
  intros x y z Hxy Hyz.
  generalize (isdecrel_leNonnegativeRationals x z) ;
    apply sumofmaps ; intros Hxz.
  - rewrite minusNonnegativeRationals_eq_zero.
    apply ispositive_minusNonnegativeRationals.
    exact Hyz.
    exact Hxz.
  - apply (notge_ltNonnegativeRationals z x) in Hxz.
    apply_pr2 (plusNonnegativeRationals_ltcompat_r z) ; rewrite !minusNonnegativeRationals_plus_r.
    exact Hxy.
    now apply lt_leNonnegativeRationals, Hyz.
    now apply lt_leNonnegativeRationals, Hxz.
Qed.
Lemma minusNonnegativeRationals_ltcompat_l' :
  ∏ x y z : NonnegativeRationals, x - z < y - z -> x < y.
Proof.
  intros x y z Hlt.
  assert (Hyz : (z < y)%NRat).
  { apply_pr2 ispositive_minusNonnegativeRationals.
    apply istrans_le_lt_ltNonnegativeRationals with (x - z).
    now apply isnonnegative_NonnegativeRationals.
    exact Hlt. }
  generalize (isdecrel_leNonnegativeRationals x z) ;
    apply sumofmaps ; intro Hxz.
  - apply istrans_le_lt_ltNonnegativeRationals with (1 := Hxz).
    exact Hyz.
  - apply notge_ltNonnegativeRationals in Hxz ;
    apply lt_leNonnegativeRationals in Hxz.
    apply lt_leNonnegativeRationals in Hyz.
    rewrite <- (minusNonnegativeRationals_plus_r _ _ Hxz), <- (minusNonnegativeRationals_plus_r _ _ Hyz).
    apply plusNonnegativeRationals_ltcompat_r.
    exact Hlt.
Qed.
Lemma minusNonnegativeRationals_ltcompat_r:
  ∏ x y z : NonnegativeRationals, x < y -> x < z -> z - y < z - x.
Proof.
  intros x y z Hxy Hxz.
  generalize (isdecrel_leNonnegativeRationals y z) ;
    apply sumofmaps ; intros Hky.
  - apply_pr2 (plusNonnegativeRationals_ltcompat_r y).
    rewrite minusNonnegativeRationals_plus_r, minusNonnegativeRationals_plus_exchange, iscomm_plusNonnegativeRationals, <- minusNonnegativeRationals_plus_exchange.
    pattern z at 1 ; rewrite <- (islunit_zeroNonnegativeRationals z).
    apply plusNonnegativeRationals_ltcompat_r.
    now apply (pr1 (ispositive_minusNonnegativeRationals _ _)), Hxy.
    now apply lt_leNonnegativeRationals, Hxy.
    now apply lt_leNonnegativeRationals, Hxz.
    exact Hky.
  - rewrite minusNonnegativeRationals_eq_zero.
    now apply (pr1 (ispositive_minusNonnegativeRationals _ _)), Hxz.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals, Hky.
Qed.
Lemma minusNonnegativeRationals_ltcompat_r':
  ∏ x y z : NonnegativeRationals, z - y < z - x -> x < y.
Proof.
  intros x y z H.
  apply notge_ltNonnegativeRationals.
  intro H0 ; revert H.
  change (neg (z - y < z - x)).
  apply notlt_geNonnegativeRationals.
  now apply minusNonnegativeRationals_lecompat_r, H0.
Qed.

(** *** Multiplication *)
(** Rewritings *)

Definition isassoc_multNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, x * y * z = x * (y * z) :=
  CommDivRig_isassoc_mult.
Definition islunit_oneNonnegativeRationals:
  ∏ x : NonnegativeRationals, 1 * x = x :=
  CommDivRig_islunit_one.
Definition isrunit_oneNonnegativeRationals:
  ∏ x : NonnegativeRationals, x * 1 = x :=
  CommDivRig_isrunit_one.
Definition iscomm_multNonnegativeRationals:
  ∏ x y : NonnegativeRationals, x * y = y * x :=
  CommDivRig_iscomm_mult.
Definition isldistr_mult_plusNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, z * (x + y) = z * x + z * y :=
  CommDivRig_isldistr.
Definition isrdistr_mult_plusNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, (x + y) * z = x * z + y * z :=
  CommDivRig_isrdistr.
Definition islabsorb_zero_multNonnegativeRationals:
  ∏ x : NonnegativeRationals, 0 * x = 0 :=
  rigmult0x _.
Definition israbsorb_zero_multNonnegativeRationals:
  ∏ x : NonnegativeRationals, x * 0 = 0 :=
  rigmultx0 _.

(** Order *)

Lemma multNonnegativeRationals_ltcompat_l :
  ∏ k x y : NonnegativeRationals, 0 < k -> (x < y) <->  (k * x < k * y).
Proof.
  intros k x y Hk.
  split ; intro H.
  - apply (hqlthandmultl (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
  - apply (hqlthandmultlinv (pr1 x) (pr1 y) (pr1 k)).
    exact Hk.
    exact H.
Qed.
Lemma multNonnegativeRationals_ltcompat_r :
  ∏ k x y : NonnegativeRationals, 0 < k -> (x < y) <-> (x * k < y * k).
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_ltcompat_l.
Qed.

Lemma multNonnegativeRationals_lecompat_l :
  ∏ k x y : NonnegativeRationals, x <= y -> k * x <= k * y.
Proof.
  intros k x y Hle.
  generalize (eq0orgt0NonnegativeRationals k) ;
    apply sumofmaps ; intros Hk0.
  - rewrite Hk0.
    rewrite !islabsorb_zero_multNonnegativeRationals.
    now apply isrefl_leNonnegativeRationals.
  - apply hqlehandmultl, Hle.
    exact Hk0.
Qed.
Lemma multNonnegativeRationals_lecompat_l' :
  ∏ k x y : NonnegativeRationals, 0 < k -> k * x <= k * y -> x <= y.
Proof.
  intros k x y Hk0.
  apply (hqlehandmultlinv (pr1 x) (pr1 y) (pr1 k)).
  exact Hk0.
Qed.
Lemma multNonnegativeRationals_lecompat_r :
  ∏ k x y : NonnegativeRationals, x <= y -> x * k <= y * k.
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_lecompat_l.
Qed.
Lemma multNonnegativeRationals_lecompat_r' :
  ∏ k x y : NonnegativeRationals, 0 < k -> x * k <= y * k -> x <= y.
Proof.
  intros k x y Hk.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  exact (multNonnegativeRationals_lecompat_l' k x y Hk).
Qed.

Lemma multNonnegativeRationals_eqcompat_l:
  ∏ k x y : NonnegativeRationals,
    0 < k -> k * x = k * y -> x = y.
Proof.
  intros k x y Hk0 H.
  rewrite <- (islunit_oneNonnegativeRationals x).
  change 1 with (1%dr : NonnegativeRationals).
  assert (Hk : k != 0).
  { apply gtNonnegativeRationals_noteq, Hk0. }
  rewrite <- (CommDivRig_islinv k Hk).
  rewrite isassoc_multNonnegativeRationals.
  rewrite H.
  rewrite <- isassoc_multNonnegativeRationals.
  change ((/ (k,, Hk))%dr * k) with (/ (k,, Hk) * k)%dr.
  rewrite (CommDivRig_islinv k Hk).
  now apply islunit_oneNonnegativeRationals.
Qed.
Lemma multNonnegativeRationals_eqcompat_r:
  ∏ k x y : NonnegativeRationals,
    0 < k -> x * k = y * k -> x = y.
Proof.
  intros k x y.
  rewrite !(iscomm_multNonnegativeRationals _ k).
  now apply multNonnegativeRationals_eqcompat_l.
Qed.

Lemma ispositive_multNonnegativeRationals:
  ∏ x y : NonnegativeRationals,
    0 < x -> 0 < y -> 0 < x * y.
Proof.
  intros x y Hx Hy.
  rewrite <- (israbsorb_zero_multNonnegativeRationals x).
  apply multNonnegativeRationals_ltcompat_l.
  exact Hx.
  exact Hy.
Qed.
Lemma multNonnegativeRationals_ltcompat:
  ∏ x x' y y' : NonnegativeRationals,
    x < x' -> y < y' -> x * y < x' * y'.
Proof.
  intros x x' y y' Hx Hy.
  generalize (eq0orgt0NonnegativeRationals x) ;
    apply sumofmaps ; intros Hx0.
  - rewrite Hx0, islabsorb_zero_multNonnegativeRationals.
    apply ispositive_multNonnegativeRationals.
    rewrite <- Hx0 ; exact Hx.
    apply istrans_le_lt_ltNonnegativeRationals with y.
    now apply isnonnegative_NonnegativeRationals.
    exact Hy.
  - apply istrans_lt_le_ltNonnegativeRationals with (x * y').
    apply multNonnegativeRationals_ltcompat_l.
    exact Hx0.
    exact Hy.
    apply multNonnegativeRationals_lecompat_r.
    now apply lt_leNonnegativeRationals.
Qed.
Lemma multNonnegativeRationals_le_lt:
  ∏ x x' y y' : NonnegativeRationals,
    0 < x -> x <= x' -> y < y' -> x * y < x' * y'.
Proof.
  intros x x' y y' Hx0 Hx Hy.
  apply istrans_lt_le_ltNonnegativeRationals with (x* y').
  - apply multNonnegativeRationals_ltcompat_l.
    exact Hx0.
    exact Hy.
  - now apply multNonnegativeRationals_lecompat_r, Hx.
Qed.
Lemma multNonnegativeRationals_lt_le:
  ∏ x x' y y' : NonnegativeRationals,
    0 < y -> x < x' -> y <= y' -> x * y < x' * y'.
Proof.
  intros x x' y y' Hy0 Hx Hy.
  apply istrans_lt_le_ltNonnegativeRationals with (x' * y).
  - apply multNonnegativeRationals_ltcompat_r.
    exact Hy0.
    exact Hx.
  - now apply multNonnegativeRationals_lecompat_l, Hy.
Qed.

Lemma multNonnegativeRationals_le1_r :
  ∏ q r : NonnegativeRationals, q <= 1 -> r * q <= r.
Proof.
  intros q r Hq.
  pattern r at 2 ; rewrite <- isrunit_oneNonnegativeRationals.
  now apply multNonnegativeRationals_lecompat_l.
Qed.
Lemma multNonnegativeRationals_le1_l :
  ∏ q r : NonnegativeRationals, q <= 1 -> q * r <= r.
Proof.
  intros q r Hq.
  pattern r at 2 ; rewrite <- islunit_oneNonnegativeRationals.
  now apply multNonnegativeRationals_lecompat_r.
Qed.

Lemma isldistr_mult_minusNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, z * (x - y) = z * x - z * y.
Proof.
  intros x y z.
  generalize (isdecrel_leNonnegativeRationals x y) ;
    apply sumofmaps ; [ intros Hle | intros Hlt].
  - rewrite !minusNonnegativeRationals_eq_zero.
    now apply israbsorb_zero_multNonnegativeRationals.
    now apply multNonnegativeRationals_lecompat_l, Hle.
    exact Hle.
  - apply notge_ltNonnegativeRationals in Hlt ;
    apply lt_leNonnegativeRationals in Hlt.
    apply plusNonnegativeRationals_eqcompat_r with (z * y).
    rewrite <- isldistr_mult_plusNonnegativeRationals.
    rewrite !minusNonnegativeRationals_plus_r.
    reflexivity.
    now apply multNonnegativeRationals_lecompat_l, Hlt.
    exact Hlt.
Qed.
Lemma isrdistr_mult_minusNonnegativeRationals:
  ∏ x y z : NonnegativeRationals, (x - y) * z = x * z - y * z.
Proof.
  intros x y z.
  rewrite !(iscomm_multNonnegativeRationals _ z).
  now apply isldistr_mult_minusNonnegativeRationals.
Qed.

(** *** Multiplicative Inverse *)
(** Rewritings *)

Definition islinv_NonnegativeRationals:
  ∏ x : NonnegativeRationals, 0 < x -> / x * x = 1.
Proof.
  intros x Hx0.
  assert (Hx : x != 0).
  { apply gtNonnegativeRationals_noteq, Hx0. }
  clear Hx0.
  revert x Hx.
  apply @CommDivRig_islinv.
Qed.
Definition isrinv_NonnegativeRationals:
  ∏ x : NonnegativeRationals, 0 < x -> x * / x = 1.
Proof.
  intros x.
  rewrite iscomm_multNonnegativeRationals.
  now apply islinv_NonnegativeRationals.
Qed.

Local Lemma inv_zeroNonnegativeRationals :
  / 0 = 0.
Proof.
  unfold zeroNonnegativeRationals, invNonnegativeRationals, hnnq_zero, hnnq_inv ; simpl pr1 ; simpl pr2.
  generalize (hqlehchoice 0%hq 0%hq (isreflhqleh 0%hq)) ;
    apply coprod_rect ; intro H0.
  - now apply fromempty ; apply isirreflhqlth in H0.
  - reflexivity.
Qed.

Lemma ispositive_invNonnegativeRationals :
  ∏ x, (0 < x) <-> (0 < / x).
Proof.
  intros x.
  split ; intro Hx.
  - apply_pr2 (multNonnegativeRationals_ltcompat_l x).
    exact Hx.
    rewrite israbsorb_zero_multNonnegativeRationals,
    isrinv_NonnegativeRationals.
    + exact ispositive_oneNonnegativeRationals.
    + apply NonnegativeRationals_neq0_gt0 ; intros Hx0.
      revert Hx ; rewrite Hx0.
      now apply isirrefl_ltNonnegativeRationals.
  - apply_pr2 (multNonnegativeRationals_ltcompat_r (/ x)).
    exact Hx.
    rewrite islabsorb_zero_multNonnegativeRationals,
    isrinv_NonnegativeRationals.
    + exact ispositive_oneNonnegativeRationals.
    + apply NonnegativeRationals_neq0_gt0 ; intros Hx0.
      revert Hx ; rewrite Hx0.
      unfold invNonnegativeRationals, hnnq_inv.
      generalize (hqlehchoice 0%hq (pr1 0) (pr2 0)).
      apply (coprod_rect (λ _, _ → _)) ; intros Hx.
      * apply fromempty ; revert Hx.
        now apply isirreflhqlth.
      * now apply isirrefl_ltNonnegativeRationals.
Qed.

Lemma isinvolutive_invNonnegativeRationals :
  ∏ x, / / x = x.
Proof.
  intros x.
  generalize (eq0orgt0NonnegativeRationals x) ;
    apply sumofmaps ; intro Hx0.
  - now rewrite Hx0, !inv_zeroNonnegativeRationals.
  - apply (multNonnegativeRationals_eqcompat_l (/ x)).
    apply ispositive_invNonnegativeRationals ; exact Hx0.
    rewrite islinv_NonnegativeRationals, isrinv_NonnegativeRationals.
    reflexivity.
    apply ispositive_invNonnegativeRationals ; exact Hx0.
    exact Hx0.
Qed.

(** Order *)

Lemma invNonnegativeRationals_lecompat :
  ∏ x y : NonnegativeRationals, 0 < x -> x <= y -> / y <= / x.
Proof.
  intros x y Hx0 Hxy.
  assert (Hy0 : 0 < y).
  { apply istrans_lt_le_ltNonnegativeRationals with x.
    exact Hx0.
    exact Hxy. }
  apply (multNonnegativeRationals_lecompat_l' x).
  exact Hx0.
  rewrite isrinv_NonnegativeRationals.
  apply (multNonnegativeRationals_lecompat_r' y).
  exact Hy0.
  rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals.
  exact Hxy.
  exact Hy0.
  exact Hx0.
Qed.
Lemma invNonnegativeRationals_lecompat' :
  ∏ x y : NonnegativeRationals, 0 < y -> / y <= / x -> x <= y.
Proof.
  intros x y Hy0 Hxy.
  rewrite <- (isinvolutive_invNonnegativeRationals x), <- (isinvolutive_invNonnegativeRationals y).
  apply invNonnegativeRationals_lecompat.
  now apply ispositive_invNonnegativeRationals.
  exact Hxy.
Qed.

Lemma invNonnegativeRationals_ltcompat :
  ∏ x y : NonnegativeRationals, 0 < x -> x < y -> / y < / x.
Proof.
  intros x y Hx0 Hxy.
  apply notge_ltNonnegativeRationals.
  intros H ; revert Hxy.
  change (neg (x < y)).
  apply notlt_geNonnegativeRationals.
  apply invNonnegativeRationals_lecompat'.
  exact Hx0.
  exact H.
Qed.
Lemma invNonnegativeRationals_ltcompat' :
  ∏ x y : NonnegativeRationals, 0 < y -> / y < / x -> x < y.
Proof.
  intros x y Hy0 Hxy.
  rewrite <- (isinvolutive_invNonnegativeRationals x), <- (isinvolutive_invNonnegativeRationals y).
  apply invNonnegativeRationals_ltcompat.
  apply ispositive_invNonnegativeRationals.
  exact Hy0.
  exact Hxy.
Qed.

Lemma issublinear_invNonnegativeRationals :
  ∏ x y : NonnegativeRationals, / (x + y) <= / x + / y.
Proof.
  intros x y.
  generalize (eq0orgt0NonnegativeRationals x) ;
    apply sumofmaps ; intros Hx0.
  rewrite Hx0, islunit_zeroNonnegativeRationals ; clear Hx0 x.
  now apply plusNonnegativeRationals_le_l.
  generalize (eq0orgt0NonnegativeRationals y) ;
    apply sumofmaps ; intros Hy0.
  rewrite Hy0, isrunit_zeroNonnegativeRationals ; clear Hy0 y.
  now apply plusNonnegativeRationals_le_r.
  apply (multNonnegativeRationals_lecompat_l' _ _ _ Hx0).
  rewrite isldistr_mult_plusNonnegativeRationals, (isrinv_NonnegativeRationals _ Hx0), !(iscomm_multNonnegativeRationals x).
  apply (multNonnegativeRationals_lecompat_l' _ _ _ Hy0).
  rewrite isldistr_mult_plusNonnegativeRationals, <- (isassoc_multNonnegativeRationals _ (/ y)%NRat), (isrinv_NonnegativeRationals _ Hy0), islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals, (iscomm_multNonnegativeRationals y).
  apply (multNonnegativeRationals_lecompat_l' (x + y)).
  now apply ispositive_plusNonnegativeRationals_l, Hx0.
  rewrite <- ! isassoc_multNonnegativeRationals , isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isldistr_mult_plusNonnegativeRationals, !isrdistr_mult_plusNonnegativeRationals, !isassoc_plusNonnegativeRationals.
  now apply plusNonnegativeRationals_le_r.
  now apply ispositive_plusNonnegativeRationals_l, Hx0.
Qed.
Lemma issublinear_invNonnegativeRationals_lt :
  ∏ x y : NonnegativeRationals, (0 < x)%NRat -> (0 < y)%NRat -> (/ (x + y) < / x + / y)%NRat.
Proof.
  intros x y Hx0 Hy0.
  apply_pr2 (multNonnegativeRationals_ltcompat_l x).
  exact Hx0.
  rewrite isldistr_mult_plusNonnegativeRationals, (isrinv_NonnegativeRationals _ Hx0), !(iscomm_multNonnegativeRationals x).
  apply_pr2 (multNonnegativeRationals_ltcompat_l y).
  exact Hy0.
  rewrite isldistr_mult_plusNonnegativeRationals, <- (isassoc_multNonnegativeRationals _ (/ y)%NRat), (isrinv_NonnegativeRationals _ Hy0), islunit_oneNonnegativeRationals, isrunit_oneNonnegativeRationals, (iscomm_multNonnegativeRationals y).
  apply_pr2 (multNonnegativeRationals_ltcompat_l (x + y)).
  apply ispositive_plusNonnegativeRationals_l.
  exact Hx0.
  rewrite <- ! isassoc_multNonnegativeRationals , isrinv_NonnegativeRationals, islunit_oneNonnegativeRationals, isldistr_mult_plusNonnegativeRationals, !isrdistr_mult_plusNonnegativeRationals, !isassoc_plusNonnegativeRationals.
  apply plusNonnegativeRationals_lt_r.
  apply ispositive_plusNonnegativeRationals_l.
  now apply ispositive_multNonnegativeRationals ; apply Hy0.
  now apply ispositive_plusNonnegativeRationals_l, Hx0.
Qed.

(** *** Division *)
(** Rewritings *)

Lemma multdivNonnegativeRationals :
  ∏ q r : NonnegativeRationals, 0 < r -> r * (q / r) = q.
Proof.
  intros q r Hr0.
  unfold divNonnegativeRationals.
  rewrite iscomm_multNonnegativeRationals, isassoc_multNonnegativeRationals.
  rewrite islinv_NonnegativeRationals.
  now apply isrunit_oneNonnegativeRationals.
  exact Hr0.
Qed.

Lemma minus_divNonnegativeRationals :
  ∏ x y : NonnegativeRationals, 0 < y -> / x - / y = (y - x) / (x * y).
Proof.
  intros x y Hy0.
  generalize (eq0orgt0NonnegativeRationals x) ;
    apply sumofmaps ; intros Hx0.
  - unfold divNonnegativeRationals.
    rewrite Hx0, islabsorb_zero_multNonnegativeRationals, inv_zeroNonnegativeRationals, israbsorb_zero_multNonnegativeRationals, minusNonnegativeRationals_zero_l.
    reflexivity.
  - apply multNonnegativeRationals_eqcompat_l with (x * y).
    apply ispositive_multNonnegativeRationals, Hy0.
    exact Hx0.
    rewrite multdivNonnegativeRationals.
    2: apply ispositive_multNonnegativeRationals, Hy0.
    rewrite isldistr_mult_minusNonnegativeRationals.
    rewrite iscomm_multNonnegativeRationals, <- isassoc_multNonnegativeRationals, islinv_NonnegativeRationals, islunit_oneNonnegativeRationals.
    2: exact Hx0.
    2: exact Hx0.
    rewrite isassoc_multNonnegativeRationals, isrinv_NonnegativeRationals, isrunit_oneNonnegativeRationals.
    reflexivity.
    exact Hy0.
Qed.

(** Order *)

Lemma ispositive_divNonnegativeRationals :
  ∏ x y, 0 < x -> 0 < y -> 0 < x / y.
Proof.
  intros x y Hx Hy.
  apply ispositive_multNonnegativeRationals.
  exact Hx.
  apply ispositive_invNonnegativeRationals.
  exact Hy.
Qed.

Lemma divNonnegativeRationals_le1 :
  ∏ q r : NonnegativeRationals, q <= r -> q / r <= 1.
Proof.
  intros q r Hrq.
  generalize (eq0orgt0NonnegativeRationals r) ;
    apply sumofmaps ; intros Hr0.
  - unfold divNonnegativeRationals.
    rewrite Hr0, inv_zeroNonnegativeRationals.
    rewrite israbsorb_zero_multNonnegativeRationals.
    now apply isnonnegative_NonnegativeRationals.
  - apply (multNonnegativeRationals_lecompat_r' r).
    exact Hr0.
    unfold divNonnegativeRationals.
    rewrite isassoc_multNonnegativeRationals, islinv_NonnegativeRationals.
    rewrite isrunit_oneNonnegativeRationals, islunit_oneNonnegativeRationals.
    exact Hrq.
    exact Hr0.
Qed.

(** ** NQhalf *)

Lemma NQhalf_double : ∏ x, x = x / 2 + x / 2.
Proof.
  intros x.
  change x with (pr1 x,,pr2 x).
  generalize (pr1 x) (pr2 x) ; clear x ; intros x Hx.
  unfold divNonnegativeRationals, invNonnegativeRationals, hnnq_inv, twoNonnegativeRationals, Rationals_to_NonnegativeRationals ; simpl pr1 ; simpl pr2.
  generalize (hqlehchoice 0%hq 2%hq (hqlthtoleh 0%hq 2%hq hq2_gt0)) ;
  apply coprod_rect ; intros H2.
  apply subtypeEquality_prop ; simpl pr1.
  rewrite !(hqmultcomm x), <- hqldistr, hqmultcomm.
  apply hqplusdiv2.
  apply fromempty ; generalize hq2_gt0.
  rewrite H2.
  now apply (isirreflhqlth 2%hq).
Qed.

Lemma ispositive_NQhalf : ∏ x, (0 < x) <-> (0 < x / 2).
Proof.
  intro x.
  split ; intro Hx.
  - apply_pr2 (multNonnegativeRationals_ltcompat_r 2).
    now apply ispositive_twoNonnegativeRationals.
    unfold divNonnegativeRationals ;
      rewrite isassoc_multNonnegativeRationals, islabsorb_zero_multNonnegativeRationals.
    rewrite islinv_NonnegativeRationals.
    now rewrite isrunit_oneNonnegativeRationals.
    now apply ispositive_twoNonnegativeRationals.
  - apply_pr2 (multNonnegativeRationals_ltcompat_r (/2)).
    apply (pr1 (ispositive_invNonnegativeRationals _)).
    now apply ispositive_twoNonnegativeRationals.
    rewrite islabsorb_zero_multNonnegativeRationals.
    exact Hx.
Qed.

(** ** NQmax *)

Definition NQmax : binop NonnegativeRationals.
Proof.
  intros x y.
  refine (sumofmaps _ _ (isdecrel_leNonnegativeRationals x y)) ; intros _.
  exact y.
  exact x.
Defined.
Lemma NQmax_eq_zero :
  ∏ x y : NonnegativeRationals, NQmax x y = 0 -> (x = 0) × (y = 0).
Proof.
  intros x y.
  unfold NQmax.
  generalize (isdecrel_leNonnegativeRationals x y).
  apply (coprod_rect (λ _, _ → _)) ; [ intros Hle | intros Hlt] ; intro H ; simpl in H ; split.
  - apply NonnegativeRationals_eq0_le0.
    apply istrans_leNonnegativeRationals with (1 := Hle).
    now rewrite H ; apply isrefl_leNonnegativeRationals.
  - exact H.
  - exact H.
  - apply NonnegativeRationals_eq0_le0 ; rewrite <- H.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma NQmax_case :
  ∏ (P : NonnegativeRationals -> UU),
  ∏ x y : NonnegativeRationals, P x -> P y -> P (NQmax x y).
Proof.
  intros P x y Hx Hy.
  unfold NQmax.
  generalize (isdecrel_leNonnegativeRationals x y).
  now apply coprod_rect.
Qed.
Lemma NQmax_case_strong :
  ∏ (P : NonnegativeRationals -> UU),
  ∏ x y : NonnegativeRationals, (y <= x -> P x) -> (x <= y -> P y) -> P (NQmax x y).
Proof.
  intros P x y Hx Hy.
  unfold NQmax.
  generalize ( isdecrel_leNonnegativeRationals x y).
  apply coprod_rect ; [intros Hle | intros Hlt].
  - now apply Hy.
  - apply Hx.
    now apply lt_leNonnegativeRationals, notge_ltNonnegativeRationals.
Qed.
Lemma iscomm_NQmax :
  ∏ x y, NQmax x y = NQmax y x.
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
  ∏ x y : NonnegativeRationals, x <= NQmax x y.
Proof.
  intros x y.
  apply NQmax_case_strong ; intro Hle.
  - apply isrefl_leNonnegativeRationals.
  - exact Hle.
Qed.
Lemma NQmax_le_r :
  ∏ x y : NonnegativeRationals, y <= NQmax x y.
Proof.
  intros x y.
  rewrite iscomm_NQmax.
  now apply NQmax_le_l.
Qed.

(** ** NQmin *)

Definition NQmin : binop NonnegativeRationals.
Proof.
  intros x y.
  refine (sumofmaps _ _ (isdecrel_leNonnegativeRationals x y)) ; intros _.
  exact x.
  exact y.
Defined.

(** ** intpart *)

Lemma nat_to_NonnegativeRationals_O :
  nat_to_NonnegativeRationals O = 0.
Proof.
  apply subtypeEquality_prop.
  reflexivity.
Qed.
Lemma nat_to_NonnegativeRationals_Sn :
  ∏ n : nat, nat_to_NonnegativeRationals (S n) = nat_to_NonnegativeRationals n + 1.
Proof.
  intro n.
  apply subtypeEquality_prop.
  simpl.
  rewrite nattohzandS, hztohqandplus.
  apply hqpluscomm.
Qed.

Definition isarchNonnegativeRationals :
  isarchrig gtNonnegativeRationals.
Proof.
  set (H := isarchhq).
  apply isarchfld_isarchring in H.
  apply isarchring_isarchrig in H.
  assert (∏ n, pr1 (nattorig (X := pr1 (CommDivRig_DivRig NonnegativeRationals)) n) = nattorig (X := pr1fld hq) n).
  { induction n as [|n IHn].
    - reflexivity.
    - rewrite !nattorigS, <- IHn.
      reflexivity. }
  repeat split.
  - intros y1 y2 Hy.
    generalize (isarchrig_diff _ H (pr1 y1) (pr1 y2) Hy).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    generalize (pr2 n) ; intros Hn.
    rewrite <- !X in Hn.
    exact Hn.
  - intros x.
    generalize (isarchrig_gt _ H (pr1 x)).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    generalize (pr2 n) ; intros Hn.
    rewrite <- X in Hn.
    exact Hn.
  - intros x.
    generalize (isarchrig_pos _ H (pr1 x)).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    generalize (pr2 n) ; intros Hn.
    rewrite <- X in Hn.
    exact Hn.
  - exact isringaddhzgth.
  - exact isringaddhzgth.
  - exact isringmulthqgth.
  - exact isirreflhqgth.
Qed.

Close Scope NRat_scope.

(** ** Opacify *)

Global Opaque NonnegativeRationals NonnegativeRationals_EffectivelyOrderedSet.

(* End of the file hnnq.v *)
