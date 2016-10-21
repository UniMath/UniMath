(** * Additionals theorems and definitions *)

Require Export UniMath.Topology.Prelim.

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.NumberSystems.RationalNumbers.
Require Export UniMath.Foundations.Algebra.Archimedean.

Open Scope hq_scope.

Notation "x <= y" := (hqleh x y) : hq_scope.
Notation "x >= y" := (hqgeh x y) : hq_scope.
Notation "x < y" := (hqlth x y) : hq_scope.
Notation "x > y" := (hqgth x y) : hq_scope.
Notation "/ x" := (hqmultinv x) : hq_scope.
Notation "x / y" := (hqdiv x y) : hq_scope.
Notation "2" := (hztohq (nattohz 2)) : hq_scope.

Lemma hzone_neg_hzzero : neg (1%hz = 0%hz).
Proof.
  confirm_not_equal isdeceqhz.
Qed.

Definition one_intdomnonzerosubmonoid : intdomnonzerosubmonoid hzintdom.
Proof.
  exists 1%hz ; simpl.
  exact hzone_neg_hzzero.
Defined.

Opaque hz.

Lemma hq2eq1plus1 : 2 = 1 + 1.
Proof.
  confirm_equal isdeceqhq.
Qed.

Lemma hq2_gt0 : 2 > 0.
Proof.
  confirm_yes hqgthdec 2 0.
Qed.

Lemma hq1_gt0 : 1 > 0.
Proof.
  confirm_yes hqgthdec 1 0.
Qed.

Lemma hq1ge0 : (0 <= 1)%hq.
Proof.
  confirm_yes hqlehdec 0 1.
Qed.

Lemma hqgth_hqneq :
  Π x y : hq, x > y -> hqneq x y.
Proof.
  intros x y Hlt Heq.
  rewrite Heq in Hlt.
  now apply isirreflhqgth with y.
Qed.

Lemma hqldistr :
  Π x y z, x * (y + z) = x * y + x * z.
Proof.
  intros x y z.
  now apply rngldistr.
Qed.

Lemma hqmult2r :
  Π x : hq, x * 2 = x + x.
Proof.
  intros x.
  now rewrite hq2eq1plus1, hqldistr, (hqmultr1 x).
Qed.

Lemma hqplusdiv2 : Π x : hq, x = (x + x) / 2.
  intros x.
  apply hqmultrcan with 2.
  now apply hqgth_hqneq, hq2_gt0.
  unfold hqdiv.
  rewrite hqmultassoc.
  rewrite (hqislinvmultinv 2).
  2: now apply hqgth_hqneq, hq2_gt0.
  rewrite (hqmultr1 (x + x)).
  apply hqmult2r.
Qed.

Lemma hqlth_between :
  Π x y : hq, x < y -> total2 (fun z => dirprod (x < z) (z < y)).
Proof.
  assert (H0 : / 2 > 0).
  { apply hqgthandmultlinv with 2.
    apply hq2_gt0.
    rewrite hqisrinvmultinv, hqmultx0.
    now apply hq1_gt0.
    now apply hqgth_hqneq, hq2_gt0.
  }
  intros x y Hlt.
  exists ((x + y) / 2).
  split.
  - pattern x at 1.
    rewrite (hqplusdiv2 x).
    unfold hqdiv.
    apply (hqlthandmultr _ _ (/ 2)).
    exact H0.
    now apply (hqlthandplusl _ _ x Hlt).
  - pattern y at 2.
    rewrite (hqplusdiv2 y).
    unfold hqdiv.
    apply (hqlthandmultr _ _ (/ 2)).
    exact H0.
    now apply (hqlthandplusr _ _ y Hlt).
Qed.

Lemma hq0lehandplus:
  Π n m : hq,
    0 <= n -> 0 <= m -> 0 <= (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.

Lemma hq0lehandmult:
  Π n m : hq, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
  intros n m.
  exact hqmultgeh0geh0.
Qed.

Lemma hq0leminus :
  Π r q : hq, r <= q -> 0 <= q - r.
Proof.
  intros r q Hr.
  apply hqlehandplusrinv with r.
  unfold hqminus.
  rewrite hqplusassoc, hqlminus.
  now rewrite hqplusl0, hqplusr0.
Qed.

Lemma hqinv_gt0 (x : hq) : 0 < x → 0 < / x.
Proof.
  unfold hqlth.
  intros x Hx.
  apply hqgthandmultlinv with x.
  - exact Hx.
  - rewrite hqmultx0.
    rewrite hqisrinvmultinv.
    + exact hq1_gt0.
    + apply hqgth_hqneq.
      exact Hx.
Qed.

Lemma hztohqandleh':
  Π n m : hz, (hztohq n <= hztohq m)%hq → hzleh n m.
Proof.
  intros n m Hle Hlt.
  simple refine (Hle _).
  apply hztohqandgth.
  exact Hlt.
Qed.
Lemma hztohqandlth':
  Π n m : hz, (hztohq n < hztohq m)%hq -> hzlth n m.
Proof.
  intros n m Hlt.
  apply neghzgehtolth.
  intro Hle.
  apply hztohqandgeh in Hle.
  apply hqgehtoneghqlth in Hle.
  apply Hle.
  exact Hlt.
Qed.

(** ** hq is archimedean *)

Lemma nattorig_nattohz :
  Π n : nat, nattorig (X := hz) n = nattohz n.
Proof.
  induction n as [|n IHn].
  - unfold nattorig, nattohz ; simpl.
    reflexivity.
  - rewrite nattorigS, IHn.
    apply pathsinv0, nattohzandS.
Qed.

Lemma nattorig_nat :
  Π n : nat, nattorig (X := natcommrig) n = n.
Proof.
  induction n as [|n IHn].
  reflexivity.
  rewrite nattorigS, IHn.
  reflexivity.
Qed.

Lemma isarchnat :
  isarchrig (X := natcommrig) natgth.
Proof.
  repeat split.
  - intros y1 y2 Hy.
    apply natlthchoice2 in Hy.
    induction Hy as [Hy | <-].
    + apply hinhpr.
      simple refine (mk_isarchrig_1_acc _ _ _ _ _).
      exact 1%nat.
      exact Hy.
    + apply hinhpr.
      simple refine (mk_isarchrig_1_acc _ _ _ _ _).
      exact 2%nat.
      rewrite nattorig_nat, !multsnm ; simpl.
      rewrite natplusr0.
      apply natgthandplusl, natgthsnn.
  - intros n.
    apply hinhpr.
    simple refine (mk_isarchrig_2_acc _ _ _ _).
    exact (S n).
    rewrite nattorig_nat.
    now apply natgthsnn.
  - intros n.
    apply hinhpr.
    simple refine (mk_isarchrig_3_acc _ _ _ _).
    exact 1%nat.
    reflexivity.
Defined.

Definition isarchhz : isarchrng (X := hz) hzgth.
Proof.
  simple refine (isarchrigtorng _ _ _ _ _ _).
  - reflexivity.
  - intros n m k.
    apply istransnatgth.
  - generalize isarchnat ; intros H.
    repeat split.
    + intros y1 y2 Hy.
      refine (hinhfun _ _).
      2: apply ((pr1 H) y1 y2).
      intros n.
      simple refine (mk_isarchrig_1_acc _ _ _ _ _).
      exact (isarchrig_1_val n).
      apply hinhpr.
      simple refine (mk_setquot_aux_acc _ _ _ _ _).
      exact O.
      rewrite !natplusr0.
      apply (isarchrig_1_pty n).
      revert Hy.
      apply hinhuniv.
      intros c.
      generalize (setquot_aux_pty c).
      apply natgthandplusrinv.
    + intros x.
      generalize ((pr1 (pr2 H)) x).
      apply hinhfun.
      intros n.
      simple refine (mk_isarchrig_2_acc _ _ _ _).
      exact (isarchrig_2_val n).
      apply hinhpr.
      simple refine (mk_setquot_aux_acc _ _ _ _ _).
      exact O.
      rewrite !natplusr0.
      exact (isarchrig_2_pty n).
    + intros x.
      generalize ((pr2 (pr2 H)) x).
      apply hinhfun.
      intros n.
      simple refine (mk_isarchrig_3_acc _ _ _ _).
      exact (isarchrig_3_val n).
      apply hinhpr.
      simple refine (mk_setquot_aux_acc _ _ _ _ _).
      exact O.
      rewrite !natplusr0.
      exact (isarchrig_3_pty n).
Qed.

Lemma isarchhq :
  isarchfld (X := hq) hqgth.
Proof.
  simple refine (isarchfldfrac hzintdom _ _ _ _ _ _ _ _).
  - exact isirreflhzgth.
  - exact istranshzgth.
  - apply isarchhz.
Qed.

Close Scope hq_scope.
