(** * A library about decidable Real Numbers *)
(** Author: Catherine LELAY. Oct 2015 - *)

Require Export UniMath.Algebra.Groups.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Orders.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.Algebra.Lattice.
Require Import UniMath.RealNumbers.Prelim.
Require Import UniMath.RealNumbers.Sets.
Require Import UniMath.RealNumbers.NonnegativeRationals.
Require Export UniMath.RealNumbers.NonnegativeReals.

Local Open Scope NR_scope.

(** ** Definition *)

(** *** [commring] *)

Definition hr_commring : commring := commrigtocommring NonnegativeReals.

Definition NR_to_hr : NonnegativeReals × NonnegativeReals → hr_commring
  := setquotpr (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals)).

Definition nat_to_hr (n : nat) : hr_commring :=
  NR_to_hr (nat_to_NonnegativeReals n,,0).

Lemma NR_to_hr_inside :
  ∏ x : NonnegativeReals × NonnegativeReals, pr1 (NR_to_hr x) x.
Proof.
  intros x.
  apply hinhpr ; simpl.
  exists 0 ; reflexivity.
Qed.

Local Lemma iscomprelfun_NRminus :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x
    → pr1 x - pr2 x = pr1 y - pr2 y.
Proof.
  intros x y H.
  apply (plusNonnegativeReals_eqcompat_l (pr2 x)).
  rewrite <- maxNonnegativeReals_minus_plus.
  apply (plusNonnegativeReals_eqcompat_l (pr2 y)).
  rewrite isrdistr_max_plusNonnegativeReals, H.
  rewrite (iscomm_plusNonnegativeReals (pr2 x) (pr2 y)), <- isrdistr_max_plusNonnegativeReals, maxNonnegativeReals_minus_plus.
  now rewrite !isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)).
Qed.

Lemma iscomprelfun_hr_to_NR :
  iscomprelfun (Y := NonnegativeReals × NonnegativeReals) (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals))
               (λ x : NonnegativeReals × NonnegativeReals,
                      pr1 x - pr2 x ,, pr2 x - pr1 x).
Proof.
  intros x y.
  apply hinhuniv'.
  refine (isasetdirprod _ _ _ _ _ _) ;
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
  intros c.
  apply dirprodeq.
  + apply iscomprelfun_NRminus.
    apply (plusNonnegativeReals_eqcompat_l (pr1 c)).
    exact (pr2 c).
  + apply (iscomprelfun_NRminus (pr2 x ,, pr1 x) (pr2 y ,, pr1 y)).
    simpl.
    rewrite (iscomm_plusNonnegativeReals (pr2 x)), (iscomm_plusNonnegativeReals (pr2 y)).
    apply (plusNonnegativeReals_eqcompat_l (pr1 c)), pathsinv0.
    exact (pr2 c).
Qed.

Definition hr_to_NR (x : hr_commring) : NonnegativeReals × NonnegativeReals.
Proof.
  revert x.
  simple refine (setquotuniv _ (_,,_) _ _).
  - apply isasetdirprod ;
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
  - intros x.
    apply (pr1 x - pr2 x ,, pr2 x - pr1 x).
  - apply iscomprelfun_hr_to_NR.
Defined.

Definition hr_to_NRpos (x : hr_commring) : NonnegativeReals := pr1 (hr_to_NR x).
Definition hr_to_NRneg (x : hr_commring) : NonnegativeReals := pr2 (hr_to_NR x).

Lemma hr_to_NR_correct :
  ∏ (x : hr_commring), pr1 x (hr_to_NR x).
Proof.
  intros X.
  generalize (pr1 (pr2 X)).
  apply hinhuniv.
  intros x.
  pattern X at 2.
  rewrite <- (setquotl0 _ X x).
  unfold hr_to_NR.
  rewrite setquotunivcomm.
  generalize (pr2 x).
  apply (pr1 (pr2 (pr2 X))).
  apply hinhpr.
  exists 0 ; simpl.
  change ((pr1 (pr1 x) + (pr2 (pr1 x) - pr1 (pr1 x)) + 0) =
   ((pr1 (pr1 x) - pr2 (pr1 x)) + pr2 (pr1 x) + 0))%NR.
  rewrite !isrunit_zero_plusNonnegativeReals.
  rewrite iscomm_plusNonnegativeReals, <- !maxNonnegativeReals_minus_plus.
  now apply iscomm_maxNonnegativeReals.
Qed.

Lemma hr_to_NRpos_NR_to_hr :
  ∏ (x : NonnegativeReals × NonnegativeReals),
    hr_to_NRpos (NR_to_hr x) = pr1 x - pr2 x.
Proof.
  intros x.
  unfold hr_to_NRpos, hr_to_NR, NR_to_hr.
  now rewrite setquotunivcomm.
Qed.
Lemma hr_to_NRneg_NR_to_hr :
  ∏ (x : NonnegativeReals × NonnegativeReals),
    hr_to_NRneg (NR_to_hr x) = pr2 x - pr1 x.
Proof.
  intros x.
  unfold hr_to_NRneg, hr_to_NR, NR_to_hr.
  now rewrite setquotunivcomm.
Qed.

Lemma hr_to_NR_bij :
  ∏ x : hr_commring, NR_to_hr (hr_to_NR x) = x.
Proof.
  intros x.
  unfold NR_to_hr.
  pattern x at 2.
  apply (setquotl0 _ x ((hr_to_NR x),,(hr_to_NR_correct x))).
Qed.

Lemma hr_to_NRposneg_zero :
  ∏ x : hr_commring, 0 < hr_to_NRpos x -> hr_to_NRneg x = 0.
Proof.
  intros x.
  rewrite <- (hr_to_NR_bij x).
  generalize (hr_to_NR x) ; clear x ; intros x.
  rewrite hr_to_NRpos_NR_to_hr, hr_to_NRneg_NR_to_hr.
  intros Hx.
  apply minusNonnegativeReals_eq_zero.
  apply lt_leNonnegativeReals.
  apply_pr2 ispositive_minusNonnegativeReals.
  exact Hx.
Qed.
Lemma hr_to_NRnegpos_zero :
  ∏ x : hr_commring, 0 < hr_to_NRneg x -> hr_to_NRpos x = 0.
Proof.
  intros x.
  rewrite <- (hr_to_NR_bij x).
  generalize (hr_to_NR x) ; clear x ; intros x.
  rewrite hr_to_NRpos_NR_to_hr, hr_to_NRneg_NR_to_hr.
  intros Hx.
  apply minusNonnegativeReals_eq_zero.
  apply lt_leNonnegativeReals.
  apply_pr2 ispositive_minusNonnegativeReals.
  exact Hx.
Qed.

Lemma hr_to_NRpos_NR_to_hr_std :
  ∏ (x : NonnegativeReals × NonnegativeReals),
    (0 < pr1 x -> pr2 x = 0) ->
    hr_to_NRpos (NR_to_hr x) = pr1 x.
Proof.
  intros x Hx.
  rewrite hr_to_NRpos_NR_to_hr.
  apply (plusNonnegativeReals_eqcompat_l (pr2 x)).
  rewrite <- maxNonnegativeReals_minus_plus.
  now apply max_plusNonnegativeReals.
Qed.
Lemma hr_to_NRneg_NR_to_hr_std :
  ∏ (x : NonnegativeReals × NonnegativeReals),
    (0 < pr1 x -> pr2 x = 0) ->
    hr_to_NRneg (NR_to_hr x) = pr2 x.
Proof.
  intros x Hx.
  rewrite hr_to_NRneg_NR_to_hr.
  apply (plusNonnegativeReals_eqcompat_l (pr1 x)).
  rewrite <- maxNonnegativeReals_minus_plus.
  rewrite iscomm_plusNonnegativeReals, iscomm_maxNonnegativeReals.
  now apply max_plusNonnegativeReals.
Qed.

(** Caracterisation of equality *)

Lemma NR_to_hr_eq :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x <-> NR_to_hr x = NR_to_hr y.
Proof.
  intros x y.
  split ; intros H.
  - apply iscompsetquotpr.
    apply hinhpr.
    exists 0.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    exact H.
  - generalize (invmap (weqpathsinsetquot _ _ _) H) ; clear H.
    apply hinhuniv'.
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
    intros (c,p); generalize p; clear p.
    apply plusNonnegativeReals_eqcompat_l.
Qed.

(** *** Constants and Operations *)

(** 0 *)

Lemma hr_to_NR_zero :
  hr_to_NR 0%ring = (0,,0).
Proof.
  unfold ringunel1, unel_is ; simpl.
  unfold hr_to_NR.
  rewrite setquotunivcomm ; simpl.
  rewrite !minusNonnegativeReals_eq_zero.
  reflexivity.
  apply isrefl_leNonnegativeReals.
Qed.

(** 1 *)

Lemma hr_to_NR_one :
  hr_to_NR 1%ring = (1,,0).
Proof.
  unfold ringunel2, unel_is ; simpl.
  unfold rigtoringunel2, hr_to_NR.
  rewrite setquotunivcomm ; simpl.
  erewrite <- minusNonnegativeReals_correct_r.
  rewrite minusNonnegativeReals_eq_zero.
  reflexivity.
  apply isnonnegative_NonnegativeReals.
  apply pathsinv0, isrunit_zero_plusNonnegativeReals.
Qed.

(** plus *)

Lemma NR_to_hr_plus :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x + NR_to_hr y)%ring = NR_to_hr (pr1 x + pr1 y ,, pr2 x + pr2 y).
Proof.
  intros x y.
  unfold BinaryOperations.op1 ; simpl.
  unfold rigtoringop1 ; simpl.
  unfold NR_to_hr.
  apply (setquotfun2comm (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals))).
Qed.

(** opp *)

Lemma NR_to_hr_opp :
  ∏ x : NonnegativeReals × NonnegativeReals,
    (- NR_to_hr x)%ring = NR_to_hr (pr2 x ,, pr1 x).
Proof.
  intros x.
  unfold ringinv1, grinv_is ; simpl.
  unfold abgrdiffinv.
  unfold NR_to_hr.
  apply (setquotfuncomm (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals))).
Qed.

Lemma hr_to_NR_opp :
  ∏ x : hr_commring,
    hr_to_NR (- x)%ring = (hr_to_NRneg x ,, hr_to_NRpos x).
Proof.
  intros x.
  rewrite <- (hr_to_NR_bij x), NR_to_hr_opp.
  unfold hr_to_NRneg, hr_to_NRpos.
  generalize (hr_to_NR x) ; clear x ; intros x.
  unfold hr_to_NR, NR_to_hr.
  rewrite !setquotunivcomm.
  reflexivity.
Qed.
Lemma hr_to_NRpos_opp :
  ∏ x : hr_commring,
    hr_to_NRpos (- x)%ring = hr_to_NRneg x.
Proof.
  intros x.
  unfold hr_to_NRpos.
  now rewrite hr_to_NR_opp.
Qed.
Lemma hr_to_NRneg_opp :
  ∏ x : hr_commring,
    hr_to_NRneg (- x)%ring = hr_to_NRpos x.
Proof.
  intros x.
  unfold hr_to_NRneg.
  now rewrite hr_to_NR_opp.
Qed.

(** minus *)

Lemma NR_to_hr_minus :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x - NR_to_hr y)%ring = NR_to_hr (pr1 x + pr2 y ,, pr2 x + pr1 y).
Proof.
  intros x y.
  rewrite NR_to_hr_opp, NR_to_hr_plus.
  reflexivity.
Qed.

Lemma hr_opp_minus :
  ∏ x y : hr_commring,
    (x - y = - ((- x) - (- y)))%ring.
Proof.
  intros x y.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij y).
  rewrite !NR_to_hr_opp, !NR_to_hr_plus, NR_to_hr_opp ; simpl.
  reflexivity.
Qed.

Lemma hr_to_NRpos_minus :
  ∏ x y : hr_commring,
    hr_to_NRpos x - hr_to_NRpos y <= hr_to_NRpos (x - y)%ring.
Proof.
  intros X Y.
  set (x := hr_to_NRpos X) ;
  set (y := hr_to_NRpos Y).
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y).
  rewrite NR_to_hr_minus.
  change (pr1 (hr_to_NR X)) with x.
  change (pr1 (hr_to_NR Y)) with y.
  change (pr2 (hr_to_NR X)) with (hr_to_NRneg X).
  change (pr2 (hr_to_NR Y)) with (hr_to_NRneg Y).
  rewrite hr_to_NRpos_NR_to_hr.
  simpl pr1 ; simpl pr2.
  apply_pr2 (plusNonnegativeReals_lecompat_l (hr_to_NRneg X + y)).
  rewrite <- maxNonnegativeReals_minus_plus.
  rewrite (iscomm_plusNonnegativeReals _ y), <- isassoc_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
  rewrite isrdistr_max_plusNonnegativeReals.
  apply maxNonnegativeReals_le.
  rewrite <- max_plusNonnegativeReals.
  apply maxNonnegativeReals_le.
  eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
  apply plusNonnegativeReals_le_l.
  eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
  apply plusNonnegativeReals_le_r.
  apply hr_to_NRposneg_zero.
  apply maxNonnegativeReals_le_r.
Qed.
Lemma hr_to_NRneg_minus :
  ∏ x y : hr_commring,
    hr_to_NRneg x - hr_to_NRneg y <= hr_to_NRneg (x - y)%ring.
Proof.
  intros x y.
  rewrite hr_opp_minus.
  pattern x at 1 ;
    rewrite <- (grinvinv hr_commring x) ;
    pattern y at 1 ;
    rewrite <- (grinvinv hr_commring y).
  change (hr_to_NRneg (- (- x))%ring - hr_to_NRneg (- (- y))%ring <=
   hr_to_NRneg (- (- x - - y))%ring).
  rewrite !hr_to_NRneg_opp.
  apply hr_to_NRpos_minus.
Qed.

(** mult *)

Lemma NR_to_hr_mult :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x * NR_to_hr y)%ring = NR_to_hr (pr1 x * pr1 y + pr2 x * pr2 y ,, pr1 x * pr2 y + pr2 x * pr1 y).
Proof.
  intros x y.
  unfold BinaryOperations.op2 ; simpl.
  unfold rigtoringop2 ; simpl.
  unfold NR_to_hr.
  apply (setquotfun2comm (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrdiff (rigaddabmonoid NonnegativeReals))).
Qed.

(** *** Order *)
(** [hr_lt_rel] *)

Local Lemma isbinophrel_ltNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) ltNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_ltcompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_ltcompat_l, Hlt.
Qed.
Definition hr_lt_rel : hrel hr_commring
  := rigtoringrel NonnegativeReals isbinophrel_ltNonnegativeReals.

Lemma NR_to_hr_lt :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y < pr1 y + pr2 x
    <-> hr_lt_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_ltcompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(** [hr_le_rel] *)

Local Lemma isbinophrel_leNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) leNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_lecompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_lecompat_l, Hlt.
Qed.
Definition hr_le_rel : hrel hr_commring
  := rigtoringrel NonnegativeReals isbinophrel_leNonnegativeReals.

Lemma NR_to_hr_le :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y <= pr1 y + pr2 x
    <-> hr_le_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_lecompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_lecompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(** Theorems about order *)

Lemma hr_notlt_le :
  ∏ X Y, ¬ hr_lt_rel X Y <-> hr_le_rel Y X.
Proof.
  intros x y.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij y).
  split ; intro H.
  - apply NR_to_hr_le.
    apply notlt_leNonnegativeReals.
    intro H0 ; apply H.
    apply NR_to_hr_lt.
    exact H0.
  - intro H0.
    refine (pr2 (notlt_leNonnegativeReals _ _) _ _).
    refine (pr2 (NR_to_hr_le _ _) _).
    apply H.
    apply_pr2 NR_to_hr_lt.
    exact H0.
Qed.

Lemma hr_lt_le :
  ∏ X Y, hr_lt_rel X Y -> hr_le_rel X Y.
Proof.
  intros x y.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij y).
  intro H.
  apply NR_to_hr_le.
  apply lt_leNonnegativeReals.
  apply_pr2 NR_to_hr_lt.
  exact H.
Qed.

Lemma isantisymm_hr_le :
  isantisymm hr_le_rel.
Proof.
  apply isantisymmabgrdiffrel.
  intros X Y Hxy Hyx.
  apply isantisymm_leNonnegativeReals.
  now split.
Qed.

Lemma isStrongOrder_hr_lt : isStrongOrder hr_lt_rel.
Proof.
  apply isStrongOrder_abgrdiff.
  repeat split.
  - exact istrans_ltNonnegativeReals.
  - exact iscotrans_ltNonnegativeReals.
  - exact isirrefl_ltNonnegativeReals.
Qed.

Lemma iscotrans_hr_lt :
  iscotrans hr_lt_rel.
Proof.
  apply iscotrans_isStrongOrder.
  apply isStrongOrder_hr_lt.
Qed.

Lemma hr_to_NR_nonnegative :
  ∏ x : hr_commring,
    (hr_to_NRneg x = 0) <-> hr_le_rel 0%ring x.
Proof.
  intros x.
  pattern x at 2.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero.
  unfold hr_to_NRneg.
  split.
  - generalize (hr_to_NR x). intros hx.
    change hx with (pr1 hx,,pr2 hx).
    generalize (pr1 hx), (pr2 hx).
    clear hx.
    intros x1 x2 ; simpl pr1 ; simpl pr2 ; clear x ; intros ->.
    apply NR_to_hr_le ; simpl.
    rewrite !isrunit_zero_plusNonnegativeReals.
    now apply isnonnegative_NonnegativeReals.
  - pattern x at 2.
    rewrite <- (hr_to_NR_bij x).
    generalize (hr_to_NR x) ; clear x ; intros x Hx.
    unfold hr_to_NR, NR_to_hr.
    rewrite setquotunivcomm ; simpl.
    apply_pr2_in NR_to_hr_le Hx.
    rewrite isrunit_zero_plusNonnegativeReals, islunit_zero_plusNonnegativeReals in Hx.
    now apply minusNonnegativeReals_eq_zero.
Qed.

Lemma hr_to_NR_positive :
  ∏ x : hr_commring,
    (hr_to_NRpos x ≠ 0 × hr_to_NRneg x = 0) <-> hr_lt_rel 0%ring x.
Proof.
  intros x.
  repeat split.
  - pattern x at 3.
    rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero.
    unfold hr_to_NRpos, hr_to_NRneg.
    change (hr_to_NR x) with (pr1 (hr_to_NR x),,pr2 _).
    generalize (pr1 (hr_to_NR x)), (pr2 (hr_to_NR x)) ;
      intros x1 x2 ; simpl pr1 ; simpl pr2 ; clear x ; intros H1 ; rewrite (pr2 H1).
    apply NR_to_hr_lt ; simpl.
    rewrite !isrunit_zero_plusNonnegativeReals.
    now apply ispositive_apNonnegativeReals, (pr1 H1).
  - rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero in X.
    apply_pr2_in NR_to_hr_lt X.
    rewrite isrunit_zero_plusNonnegativeReals, islunit_zero_plusNonnegativeReals in X.
    apply_pr2 ispositive_apNonnegativeReals.
    eapply istrans_le_lt_ltNonnegativeReals, X.
    now apply isnonnegative_NonnegativeReals.
  - apply_pr2 hr_to_NR_nonnegative.
    now apply hr_lt_le.
Qed.

Lemma hr_to_NR_nonpositive :
  ∏ x : hr_commring,
    (hr_to_NRpos x = 0) <-> hr_le_rel x 0%ring.
Proof.
  intros x.
  pattern x at 2.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero.
  unfold hr_to_NRpos.
  split.
  - change (hr_to_NR x) with (pr1 (hr_to_NR x),,pr2 _).
    simpl pr1 ; simpl pr2 ; intros ->.
    apply NR_to_hr_le ; simpl.
    rewrite !islunit_zero_plusNonnegativeReals.
    now apply isnonnegative_NonnegativeReals.
  - pattern x at 2.
    rewrite <- (hr_to_NR_bij x).
    generalize (hr_to_NR x) ; clear x ; intros x Hx.
    unfold hr_to_NR, NR_to_hr.
    rewrite setquotunivcomm ; simpl.
    apply_pr2_in NR_to_hr_le Hx.
    rewrite isrunit_zero_plusNonnegativeReals, islunit_zero_plusNonnegativeReals in Hx.
    now apply minusNonnegativeReals_eq_zero.
Qed.

Lemma hr_to_NR_negative :
  ∏ x : hr_commring,
    (hr_to_NRpos x = 0 × hr_to_NRneg x ≠ 0) <-> hr_lt_rel x 0%ring.
Proof.
  intros x.
  repeat split.
  - pattern x at 3.
    rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero.
    unfold hr_to_NRpos, hr_to_NRneg.
    change (hr_to_NR x) with (pr1 (hr_to_NR x),,pr2 _).
    simpl pr1 ; simpl pr2 ; intros H2 ; rewrite (pr1 H2).
    apply NR_to_hr_lt ; simpl.
    rewrite !islunit_zero_plusNonnegativeReals.
    now apply ispositive_apNonnegativeReals, (pr2 H2).
  - apply_pr2 hr_to_NR_nonpositive.
    now apply hr_lt_le.
  - rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%ring), hr_to_NR_zero in X.
    apply_pr2_in NR_to_hr_lt X.
    rewrite isrunit_zero_plusNonnegativeReals, islunit_zero_plusNonnegativeReals in X.
    apply_pr2 ispositive_apNonnegativeReals.
    eapply istrans_le_lt_ltNonnegativeReals, X.
    now apply isnonnegative_NonnegativeReals.
Qed.

Lemma hr_plus_ltcompat_l :
  ∏ x y z : hr_commring, hr_lt_rel y z <-> hr_lt_rel (y+x)%ring (z+x)%ring.
Proof.
  intros X Y Z.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_plus.
  split ; intro Hlt.
  - apply NR_to_hr_lt ; simpl.
    rewrite !(iscomm_plusNonnegativeReals _ (pr1 (hr_to_NR X))), !isassoc_plusNonnegativeReals.
    apply plusNonnegativeReals_ltcompat_r.
    rewrite <- ! isassoc_plusNonnegativeReals.
    apply plusNonnegativeReals_ltcompat_l.
    now apply_pr2 NR_to_hr_lt.
  - apply NR_to_hr_lt ; simpl.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 (hr_to_NR X))).
    apply_pr2 (plusNonnegativeReals_ltcompat_r (pr1 (hr_to_NR X))).
    rewrite <- ! isassoc_plusNonnegativeReals.
    rewrite !(iscomm_plusNonnegativeReals (pr1 (hr_to_NR X))), !(isassoc_plusNonnegativeReals (_ + pr1 (hr_to_NR X))).
    now apply_pr2_in NR_to_hr_lt Hlt.
Qed.
Lemma hr_plus_ltcompat_r :
  ∏ x y z : hr_commring, hr_lt_rel y z <-> hr_lt_rel (x + y)%ring (x + z)%ring.
Proof.
  intros x y z.
  rewrite !(ringcomm1 _ x).
  apply hr_plus_ltcompat_l.
Qed.

Lemma hr_plus_lecompat_l :
  ∏ x y z : hr_commring, hr_le_rel y z <-> hr_le_rel (y + x)%ring (z + x)%ring.
Proof.
  intros x y z ; split ; intro Hle.
  - apply hr_notlt_le.
    apply_pr2_in hr_notlt_le Hle.
    intro Hlt ; apply Hle.
    apply_pr2 (hr_plus_ltcompat_l x).
    exact Hlt.
  - apply hr_notlt_le.
    apply_pr2_in hr_notlt_le Hle.
    intro Hlt ; apply Hle.
    apply hr_plus_ltcompat_l.
    exact Hlt.
Qed.
Lemma hr_plus_lecompat_r :
  ∏ x y z : hr_commring, hr_le_rel y z <-> hr_le_rel (x + y)%ring (x + z)%ring.
Proof.
  intros x y z.
  rewrite !(ringcomm1 _ x).
  apply hr_plus_lecompat_l.
Qed.

Lemma hr_mult_ltcompat_l :
  ∏ x y z : hr_commring, hr_lt_rel 0%ring x -> hr_lt_rel y z -> hr_lt_rel (y * x)%ring (z * x)%ring.
Proof.
  intros X Y Z Hx0 Hlt.
  apply_pr2_in hr_to_NR_positive Hx0.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_mult ; simpl pr1 ; simpl pr2.
  change (pr2 (hr_to_NR X)) with (hr_to_NRneg X) ;
  rewrite (pr2 Hx0).
  rewrite !israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
  apply NR_to_hr_lt ; simpl.
  rewrite <- !isrdistr_plus_multNonnegativeReals.
  apply multNonnegativeReals_ltcompat_l.
  apply ispositive_apNonnegativeReals.
  exact (pr1 Hx0).
  apply_pr2 NR_to_hr_lt.
  now rewrite !hr_to_NR_bij.
Qed.
Lemma hr_mult_ltcompat_l' :
  ∏ x y z : hr_commring, hr_le_rel 0%ring x -> hr_lt_rel (y * x)%ring (z * x)%ring -> hr_lt_rel y z.
Proof.
  intros X Y Z Hx0.
  apply_pr2_in hr_to_NR_nonnegative Hx0.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_mult ; simpl pr1 ; simpl pr2.
  change (pr2 (hr_to_NR X)) with (hr_to_NRneg X).
  rewrite Hx0.
  rewrite !israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
  intros Hlt.
  apply NR_to_hr_lt.
  apply multNonnegativeReals_ltcompat_l' with (pr1 (hr_to_NR X)).
  rewrite !isrdistr_plus_multNonnegativeReals.
  now apply_pr2_in NR_to_hr_lt Hlt.
Qed.
Lemma hr_mult_ltcompat_r' :
  ∏ x y z : hr_commring, hr_le_rel 0%ring x -> hr_lt_rel (x * y)%ring (x * z)%ring -> hr_lt_rel y z.
Proof.
  intros x y z.
  rewrite !(ringcomm2 _ x).
  apply hr_mult_ltcompat_l'.
Qed.

Lemma hr_mult_lecompat_l :
  ∏ x y z : hr_commring, hr_le_rel 0%ring x -> hr_le_rel y z -> hr_le_rel (y * x)%ring (z * x)%ring.
Proof.
  intros x y z Hx0 Hle.
  apply hr_notlt_le.
  apply_pr2_in hr_notlt_le Hle.
  intro Hlt ; apply Hle.
  apply (hr_mult_ltcompat_l' x).
  exact Hx0.
  exact Hlt.
Qed.
Lemma hr_mult_lecompat_l' :
  ∏ x y z : hr_commring, hr_lt_rel 0%ring x -> hr_le_rel (y * x)%ring (z * x)%ring -> hr_le_rel y z.
Proof.
  intros x y z Hx0 Hle.
  apply hr_notlt_le.
  apply_pr2_in hr_notlt_le Hle.
  intro Hlt ; apply Hle.
  apply (hr_mult_ltcompat_l x).
  exact Hx0.
  exact Hlt.
Qed.
Lemma hr_mult_lecompat_r :
  ∏ x y z : hr_commring, hr_le_rel 0%ring x -> hr_le_rel y z -> hr_le_rel (x * y)%ring (x * z)%ring.
Proof.
  intros x y z.
  rewrite !(ringcomm2 _ x).
  apply hr_mult_lecompat_l.
Qed.
Lemma hr_mult_lecompat_r' :
  ∏ x y z : hr_commring, hr_lt_rel 0%ring x -> hr_le_rel (x * y)%ring (x * z)%ring -> hr_le_rel y z.
Proof.
  intros x y z.
  rewrite !(ringcomm2 _ x).
  apply hr_mult_lecompat_l'.
Qed.

(** *** Appartness *)

Local Lemma isbinophrel_apNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) apNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_apcompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_apcompat_l, Hlt.
Qed.
Definition hr_ap_rel : hrel hr_commring
  := rigtoringrel NonnegativeReals isbinophrel_apNonnegativeReals.

Lemma NR_to_hr_ap :
  ∏ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y ≠ pr1 y + pr2 x
    <-> hr_ap_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_apcompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_apcompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(** Theorems about apartness *)

Lemma hr_ap_lt :
  ∏ X Y : hr_commring, hr_ap_rel X Y <-> (hr_lt_rel X Y) ⨿ (hr_lt_rel Y X).
Proof.
  intros X Y.
  rewrite <-  (hr_to_NR_bij X), <- (hr_to_NR_bij Y).
  split ; intro Hap.
  - apply_pr2_in NR_to_hr_ap Hap.
    revert Hap.
    apply sumofmaps ; intros Hlt.
    + now left ; apply NR_to_hr_lt.
    + now right ; apply NR_to_hr_lt.
  - apply NR_to_hr_ap.
    revert Hap ; apply sumofmaps ; intros Hlt.
    + now left ; apply_pr2 NR_to_hr_lt.
    + now right ; apply_pr2 NR_to_hr_lt.
Qed.

Lemma istightap_hr_ap : istightap hr_ap_rel.
Proof.
  repeat split.
  - intros X Hap.
    rewrite <- (hr_to_NR_bij X) in Hap.
    apply_pr2_in NR_to_hr_ap Hap.
    revert Hap.
    now apply isirrefl_apNonnegativeReals.
  - intros X Y.
    rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y).
    intros Hap.
    apply NR_to_hr_ap.
    apply issymm_apNonnegativeReals.
    now apply_pr2 NR_to_hr_ap.
  - intros X Y Z Hap.
    apply hr_ap_lt in Hap.
    revert Hap ; apply sumofmaps ; intros Hlt.
    + apply (iscotrans_hr_lt X Y Z) in Hlt.
      revert Hlt ; apply hinhfun ; apply sumofmaps ; intros Hlt.
      * left ; apply_pr2 hr_ap_lt.
        now left.
      * right ; apply_pr2 hr_ap_lt.
        now left.
    + apply (iscotrans_hr_lt _ Y _) in Hlt.
      revert Hlt ; apply hinhfun ; apply sumofmaps ; intros Hlt.
      * right ; apply_pr2 hr_ap_lt.
        now right.
      * left ; apply_pr2 hr_ap_lt.
        now right.
  - intros X Y Hap.
    apply isantisymm_hr_le.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now right.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now left.
Qed.

(** Structures *)

Lemma islapbinop_plus : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  intro Hap.
  apply_pr2 hr_ap_lt.
  apply hr_ap_lt in Hap.
  revert Hap ; apply sumofmaps ; intros Hlt.
  - left.
    apply_pr2 (hr_plus_ltcompat_l X).
    exact Hlt.
  - right.
    apply_pr2 (hr_plus_ltcompat_l X).
    exact Hlt.
Qed.
Lemma israpbinop_plus : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z Hap.
  apply islapbinop_plus with X.
  rewrite !(ringcomm1 _ _ X).
  exact Hap.
Qed.

Lemma islapbinop_mult : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z), !NR_to_hr_mult.
  intros Hap.
  apply_pr2_in NR_to_hr_ap Hap ; simpl in Hap.
  cut (∏ Y Z, (pr1 (hr_to_NR Z) * pr1 (hr_to_NR X) + pr2 (hr_to_NR Z) * pr2 (hr_to_NR X) + (pr1 (hr_to_NR Y) * pr2 (hr_to_NR X) + pr2 (hr_to_NR Y) * pr1 (hr_to_NR X)))
       = (pr1 (hr_to_NR Z) + pr2 (hr_to_NR Y)) * pr1 (hr_to_NR X) + (pr2 (hr_to_NR Z) + pr1 (hr_to_NR Y)) * pr2 (hr_to_NR X)).
  intro H ; simpl in H,Hap ; rewrite !H in Hap ; clear H.
  apply ap_plusNonnegativeReals in Hap.
  apply NR_to_hr_ap.
  revert Hap ; apply hinhuniv ; apply sumofmaps ; intros Hap.
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; apply sumofmaps ; intros Hap.
    + exact Hap.
    + now eapply fromempty, (isirrefl_apNonnegativeReals _), Hap .
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; apply sumofmaps ; intros Hap.
    + rewrite (iscomm_plusNonnegativeReals (pr1 (hr_to_NR Z))), iscomm_plusNonnegativeReals.
      now apply issymm_apNonnegativeReals, Hap.
    + now eapply fromempty, (isirrefl_apNonnegativeReals _), Hap.
  - clear ; intros Y Z.
    rewrite !isrdistr_plus_multNonnegativeReals.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    reflexivity.
Qed.
Lemma israpbinop_mult : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z Hap.
  apply islapbinop_mult with X.
  rewrite !(ringcomm2 _ _ X).
  exact Hap.
Qed.

Lemma hr_ap_0_1 :
  isnonzeroCR hr_commring (hr_ap_rel,, istightap_hr_ap).
Proof.
  change (hr_ap_rel 1%ring 0%ring).
  rewrite <- (hr_to_NR_bij 1%ring), <- (hr_to_NR_bij 0%ring), hr_to_NR_one, hr_to_NR_zero.
  apply NR_to_hr_ap.
  rewrite !isrunit_zero_plusNonnegativeReals.
  apply isnonzeroNonnegativeReals.
Qed.

Lemma hr_islinv_neg :
  ∏ (x : hr_commring) (Hap : hr_lt_rel x 0%ring),
   (NR_to_hr (0%NR,, invNonnegativeReals (hr_to_NRneg x) (pr2 (pr2 (hr_to_NR_negative _) Hap))) * x)%ring = 1%ring.
Proof.
  intros x Hap.
  pattern x at 3;
    rewrite <- (hr_to_NR_bij x).
  rewrite NR_to_hr_mult ; simpl.
  rewrite  !islabsorb_zero_multNonnegativeReals , !islunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  rewrite <- (hr_to_NR_bij 1%ring), hr_to_NR_one.
  apply maponpaths.
  apply maponpaths.
  erewrite <- israbsorb_zero_multNonnegativeReals.
  apply maponpaths.
  apply (pr1 (pr2 (hr_to_NR_negative x) Hap)).
Qed.
Lemma hr_isrinv_neg :
  ∏ (x : hr_commring) (Hap : hr_lt_rel x 0%ring),
   (x * NR_to_hr (0%NR,, invNonnegativeReals (hr_to_NRneg x) (pr2 (pr2 (hr_to_NR_negative _) Hap))))%ring = 1%ring.
Proof.
  intros x Hap.
  rewrite ringcomm2.
  now apply (hr_islinv_neg x Hap).
Qed.

Lemma hr_islinv_pos :
  ∏ (x : hr_commring) (Hap : hr_lt_rel 0%ring x),
   (NR_to_hr (invNonnegativeReals (hr_to_NRpos x) (pr1 (pr2 (hr_to_NR_positive _) Hap)) ,, 0%NR) * x)%ring = 1%ring.
Proof.
  intros x Hap.
  pattern x at 3;
    rewrite <- (hr_to_NR_bij x).
  rewrite NR_to_hr_mult ; simpl.
  rewrite  !islabsorb_zero_multNonnegativeReals , !isrunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  rewrite <- (hr_to_NR_bij 1%ring), hr_to_NR_one.
  apply maponpaths.
  apply maponpaths.
  erewrite <- israbsorb_zero_multNonnegativeReals.
  apply maponpaths.
  apply (pr2 (pr2 (hr_to_NR_positive x) Hap)).
Qed.
Lemma hr_isrinv_pos :
  ∏ (x : hr_commring) (Hap : hr_lt_rel 0%ring x),
   (x * NR_to_hr (invNonnegativeReals (hr_to_NRpos x) (pr1 (pr2 (hr_to_NR_positive _) Hap)) ,, 0%NR))%ring = 1%ring.
Proof.
  intros x Hap.
  rewrite ringcomm2.
  now apply (hr_islinv_pos x Hap).
Qed.

Lemma hr_ex_inv :
  ∏ x : hr_commring,
    hr_ap_rel x 0%ring -> multinvpair hr_commring x.
Proof.
  intros x Hap.
  generalize (pr1 (hr_ap_lt _ _) Hap) ;
    apply sumofmaps ; intros Hlt ; simpl.
  - eexists ; split.
    refine (hr_islinv_neg _ _).
    exact Hlt.
    exact (hr_isrinv_neg _ _).
  - eexists ; split.
    refine (hr_islinv_pos _ _).
    exact Hlt.
    exact (hr_isrinv_pos _ _).
Defined.

Definition hr_ConstructiveField : ConstructiveField.
Proof.
  exists hr_commring.
  exists (_,,istightap_hr_ap).
  repeat split.
  - exact islapbinop_plus.
  - exact israpbinop_plus.
  - exact islapbinop_mult.
  - exact israpbinop_mult.
  - exact hr_ap_0_1.
  - exact hr_ex_inv.
Defined.

(** ** hr_abs *)

Definition hr_abs (x : hr_ConstructiveField) : NonnegativeReals :=
  maxNonnegativeReals (hr_to_NRpos x) (hr_to_NRneg x).

Lemma NR_to_hr_abs :
  ∏ x : NonnegativeReals × NonnegativeReals,
    hr_abs (NR_to_hr x) <= maxNonnegativeReals (pr1 x) (pr2 x).
Proof.
  intros x.
  unfold hr_abs.
  rewrite hr_to_NRpos_NR_to_hr, hr_to_NRneg_NR_to_hr.
  apply maxNonnegativeReals_le.
  - eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
    now apply minusNonnegativeReals_le.
  - eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
    now apply minusNonnegativeReals_le.
Qed.

Lemma hr_abs_opp :
  ∏ x : hr_ConstructiveField, hr_abs (- x)%ring = hr_abs x.
Proof.
  intros x.
  unfold hr_abs.
  rewrite hr_to_NRpos_opp, hr_to_NRneg_opp.
  apply iscomm_maxNonnegativeReals.
Qed.

Lemma istriangle_hr_abs :
  ∏ x y : hr_ConstructiveField,
    hr_abs (x + y)%ring <= hr_abs x + hr_abs y.
Proof.
  intros x y.
  pattern x at 1 ; rewrite <- (hr_to_NR_bij x) ;
  pattern y at 1 ; rewrite <- (hr_to_NR_bij y).
  rewrite NR_to_hr_plus.
  eapply istrans_leNonnegativeReals.
  apply NR_to_hr_abs.
  apply maxNonnegativeReals_le ; apply plusNonnegativeReals_lecompat.
  apply maxNonnegativeReals_le_l.
  apply maxNonnegativeReals_le_l.
  apply maxNonnegativeReals_le_r.
  apply maxNonnegativeReals_le_r.
Qed.

Lemma istriangle_hr_abs' :
  ∏ x y : hr_ConstructiveField,
    hr_abs x - hr_abs y <= hr_abs (x + y)%ring.
Proof.
  intros x y.
  apply_pr2 (plusNonnegativeReals_lecompat_l (hr_abs y)).
  rewrite <- maxNonnegativeReals_minus_plus.
  apply maxNonnegativeReals_le.
  - assert (Hx : x = ((x + y) + (- y))%ring).
    { now rewrite ringassoc1, ringrinvax1, ringrunax1. }
    pattern x at 1 ; rewrite Hx.
    rewrite <- (hr_abs_opp y).
    apply istriangle_hr_abs.
  - apply plusNonnegativeReals_le_r.
Qed.

Lemma hr_abs_minus :
  ∏ x y : hr_ConstructiveField,
    hr_abs x - hr_abs y <= hr_abs (x - y)%ring.
Proof.
  intros x y.
  rewrite <- (hr_abs_opp y).
  apply istriangle_hr_abs'.
Qed.

Lemma multNonnegativeReals_lecompat :
  ∏ x y z t : NonnegativeReals, x <= y -> z <= t -> x * z <= y * t.
Proof.
  intros x y z t H H0.
  eapply istrans_leNonnegativeReals, multNonnegativeReals_lecompat_l', H.
  apply multNonnegativeReals_lecompat_r', H0.
Qed.
Lemma ispositive_multNonnegativeReals :
  ∏ x y : NonnegativeReals, 0 < x ∧ 0 < y <-> 0 < x * y.
Proof.
  intros x y.
  split.
  - intros H.
    rewrite <- (islabsorb_zero_multNonnegativeReals y).
    apply multNonnegativeReals_ltcompat_l.
    apply (pr2 H).
    apply (pr1 H).
  - intros H ; split.
    eapply multNonnegativeReals_ltcompat_l'.
    rewrite islabsorb_zero_multNonnegativeReals.
    exact H.
    eapply multNonnegativeReals_ltcompat_r'.
    rewrite israbsorb_zero_multNonnegativeReals.
    exact H.
Qed.
Lemma maxNonnegativeReals_lt' :
  ∏ x y z : NonnegativeReals,
    z < maxNonnegativeReals x y -> z < x ∨ z < y.
Proof.
  intros x y z.
  intros H.
  generalize (iscotrans_ltNonnegativeReals _ x _ H).
  apply hinhfun.
  apply sumofmaps ;
  intros Hx.
  - now left.
  - right.
    rewrite <- (maxNonnegativeReals_carac_r x y).
    apply H.
    apply notlt_leNonnegativeReals ; intros Hy.
    apply (isirrefl_ltNonnegativeReals (maxNonnegativeReals x y)).
    apply maxNonnegativeReals_lt.
    exact Hx.
    now apply istrans_ltNonnegativeReals with x.
Qed.

Lemma hr_abs_mult :
  ∏ x y : hr_ConstructiveField, hr_abs (x * y)%ring = hr_abs x * hr_abs y.
Proof.
  intros x y.
  pattern x at 1 ; rewrite <- (hr_to_NR_bij x) ;
  pattern y at 1 ; rewrite <- (hr_to_NR_bij y).
  rewrite NR_to_hr_mult.
  change (pr1 (hr_to_NR x)) with (hr_to_NRpos x) ;
    change (pr1 (hr_to_NR y)) with (hr_to_NRpos y) ;
    change (pr2 (hr_to_NR x)) with (hr_to_NRneg x) ;
    change (pr2 (hr_to_NR y)) with (hr_to_NRneg y).
  rewrite <- !max_plusNonnegativeReals.
  unfold hr_abs.
  rewrite hr_to_NRpos_NR_to_hr_std, hr_to_NRneg_NR_to_hr_std ; simpl.
  - rewrite isldistr_max_multNonnegativeReals, !isrdistr_max_multNonnegativeReals.
    rewrite !isassoc_maxNonnegativeReals.
    apply maponpaths.
    rewrite iscomm_maxNonnegativeReals, !isassoc_maxNonnegativeReals.
    rewrite iscomm_maxNonnegativeReals, !isassoc_maxNonnegativeReals.
    apply maponpaths.
    apply iscomm_maxNonnegativeReals.
  - intros H.
    apply maxNonnegativeReals_lt' in H.
    apply le0_NonnegativeReals.
    revert H ; apply hinhuniv ; apply sumofmaps ; intros H ;
    apply_pr2_in ispositive_multNonnegativeReals H ;
    apply maxNonnegativeReals_le ;
    apply_pr2 le0_NonnegativeReals.
    now rewrite (hr_to_NRposneg_zero _ (pr2 H)), israbsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRposneg_zero _ (pr1 H)), islabsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRnegpos_zero _ (pr1 H)), islabsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRnegpos_zero _ (pr2 H)), israbsorb_zero_multNonnegativeReals.
  - intros H.
    apply maxNonnegativeReals_lt' in H.
    apply le0_NonnegativeReals.
    revert H ; apply hinhuniv ; apply sumofmaps ; intros H ;
    apply_pr2_in ispositive_multNonnegativeReals H ;
    apply maxNonnegativeReals_le ;
    apply_pr2 le0_NonnegativeReals.
    now rewrite (hr_to_NRposneg_zero _ (pr2 H)), israbsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRposneg_zero _ (pr1 H)), islabsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRnegpos_zero _ (pr1 H)), islabsorb_zero_multNonnegativeReals.
    now rewrite (hr_to_NRnegpos_zero _ (pr2 H)), israbsorb_zero_multNonnegativeReals.
  - intros H.
    apply_pr2_in ispositive_multNonnegativeReals H.
    rewrite hr_to_NRposneg_zero.
    apply islabsorb_zero_multNonnegativeReals.
    exact (pr1 H).
  - intros H.
    apply_pr2_in ispositive_multNonnegativeReals H.
    rewrite hr_to_NRposneg_zero.
    apply islabsorb_zero_multNonnegativeReals.
    exact (pr1 H).
Qed.

(** ** Archimedean *)

Lemma nat_to_hr_O :
  nat_to_hr O = 0%ring.
Proof.
  unfold nat_to_hr.
  rewrite nat_to_NonnegativeReals_O.
  reflexivity.
Qed.

Lemma nat_to_hr_S :
  ∏ n : nat, nat_to_hr (S n) = (1 + nat_to_hr n)%ring.
Proof.
  intros n.
  unfold nat_to_hr.
  rewrite nat_to_NonnegativeReals_Sn, iscomm_plusNonnegativeReals.
  rewrite <- (hr_to_NR_bij 1%ring), hr_to_NR_one, NR_to_hr_plus.
  rewrite !isrunit_zero_plusNonnegativeReals.
  reflexivity.
Qed.

Lemma hr_archimedean :
  isarchCF (λ x y : hr_ConstructiveField, hr_lt_rel y x).
Proof.
  assert (Hadd : @isbinophrel (rigaddabmonoid NonnegativeReals) gtNonnegativeReals).
  { split ; intros a b c.
    apply plusNonnegativeReals_ltcompat_r.
    apply plusNonnegativeReals_ltcompat_l. }
  assert (Htra : istrans gtNonnegativeReals).
  { intros a b c Hab Hbc.
    now apply istrans_ltNonnegativeReals with b. }
  assert (Harch : isarchrig (@setquot_aux (rigaddabmonoid NonnegativeReals) gtNonnegativeReals)).
  { set (H := NonnegativeReals_Archimedean).
    repeat split.
    - intros y1 y2.
      apply hinhuniv.
      intros c.
      generalize (pr2 c) ; intros Hc.
      apply_pr2_in plusNonnegativeReals_ltcompat_l Hc.
      generalize (isarchrig_diff _ H _ _ Hc).
      apply hinhfun.
      intros n.
      exists (pr1 n).
      apply hinhpr.
      exists 0%NR.
      apply plusNonnegativeReals_ltcompat_l.
      exact (pr2 n).
    - intros x.
      generalize (isarchrig_gt _ H x).
      apply hinhfun.
      intros n.
      exists (pr1 n).
      apply hinhpr.
      exists 0%NR.
      apply plusNonnegativeReals_ltcompat_l.
      exact (pr2 n).
    - intros x.
      generalize (isarchrig_pos _ H x).
      apply hinhfun.
      intros n.
      exists (pr1 n).
      apply hinhpr.
      exists 0%NR.
      apply plusNonnegativeReals_ltcompat_l.
      exact (pr2 n). }
  intros x.
  generalize (isarchring_isarchCF (X := hr_ConstructiveField) _ (isarchrigtoring NonnegativeReals gtNonnegativeReals ispositive_oneNonnegativeReals Hadd Htra Harch) x).
  apply hinhfun.
  intros n.
  exists (pr1 n).
  generalize (pr1 n) (pr2 n) ; clear n ; intros n Hn.
  simpl pr1.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij (@nattoring hr_ConstructiveField n)) in Hn |- *.
  revert Hn.
  apply hinhfun ; simpl.
  intros c.
  exact c.
Qed.

(** ** Completeness *)

Definition Cauchy_seq (u : nat → hr_ConstructiveField) : hProp.
Proof.
  apply (make_hProp (∏ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∏ n m : nat, N ≤ n -> N ≤ m -> hr_abs (u m - u n)%ring < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.

Lemma Cauchy_seq_pr1 (u : nat → hr_ConstructiveField) :
  let x := λ n : nat, hr_to_NRpos (u n) in
  Cauchy_seq u → NonnegativeReals.Cauchy_seq x.
Proof.
  intros x.
  set (y := λ n : nat, hr_to_NRneg (u n)).
  assert (Hxy : ∏ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    unfold x, y, hr_to_NRpos, hr_to_NRneg.
    apply hr_to_NR_bij. }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros N.
  exists (pr1 N) ; intros n m Hn Hm.
  generalize ((pr2 N) _ _ Hn Hm) ; intros Hu.
  split.
  - apply (plusNonnegativeReals_ltcompat_r (x m)) in Hu.
    eapply istrans_le_lt_ltNonnegativeReals, Hu.
    rewrite hr_opp_minus, hr_abs_opp, ringcomm1.
    change (- - u n)%ring with (grinv hr_commring (grinv hr_commring (u n))).
    rewrite (grinvinv hr_commring (u n)).
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, maxNonnegativeReals_le_l.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, hr_to_NRpos_minus.
    change (hr_to_NRpos (u n)) with (x n) ;
      change (hr_to_NRpos (u m)) with (x m).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    now apply maxNonnegativeReals_le_l.
  - apply (plusNonnegativeReals_ltcompat_r (x n)) in Hu.
    eapply istrans_le_lt_ltNonnegativeReals, Hu.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, maxNonnegativeReals_le_l.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, hr_to_NRpos_minus.
    change (hr_to_NRpos (u n)) with (x n) ;
      change (hr_to_NRpos (u m)) with (x m).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    now apply maxNonnegativeReals_le_l.
Qed.
Lemma Cauchy_seq_pr2 (u : nat → hr_ConstructiveField) :
  let y := λ n : nat, hr_to_NRneg (u n) in
  Cauchy_seq u → NonnegativeReals.Cauchy_seq y.
Proof.
  intros y.
  set (x := λ n : nat, hr_to_NRpos (u n)).
  assert (Hxy : ∏ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    unfold x, y, hr_to_NRpos, hr_to_NRneg.
    apply hr_to_NR_bij. }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros N.
  exists (pr1 N) ; intros n m Hn Hm.
  generalize ((pr2 N) _ _ Hn Hm) ; intros Hu.
  split.
  - apply (plusNonnegativeReals_ltcompat_r (y m)) in Hu.
    eapply istrans_le_lt_ltNonnegativeReals, Hu.
    rewrite hr_opp_minus, hr_abs_opp, ringcomm1.
    change (- - u n)%ring with (grinv hr_commring (grinv hr_commring (u n))).
    rewrite (grinvinv hr_commring (u n)).
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, maxNonnegativeReals_le_r.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, hr_to_NRneg_minus.
    change (hr_to_NRneg (u n)) with (y n) ;
      change (hr_to_NRneg (u m)) with (y m).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    now apply maxNonnegativeReals_le_l.
  - apply (plusNonnegativeReals_ltcompat_r (y n)) in Hu.
    eapply istrans_le_lt_ltNonnegativeReals, Hu.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, maxNonnegativeReals_le_r.
    eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, hr_to_NRneg_minus.
    change (hr_to_NRneg (u n)) with (y n) ;
      change (hr_to_NRneg (u m)) with (y m).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    now apply maxNonnegativeReals_le_l.
Qed.

Definition is_lim_seq (u : nat → hr_ConstructiveField) (l : hr_ConstructiveField) : hProp.
Proof.
  apply (make_hProp (∏ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∏ n : nat, N ≤ n -> hr_abs (u n - l)%ring < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.
Definition ex_lim_seq (u : nat → hr_ConstructiveField) := ∑ l, is_lim_seq u l.

Lemma Cauchy_seq_impl_ex_lim_seq (u : nat → hr_ConstructiveField) :
  Cauchy_seq u → ex_lim_seq u.
Proof.
  intros Cu.
  set (x := λ n, hr_to_NRpos (u n)).
  set (y := λ n, hr_to_NRneg (u n)).
  assert (Hxy : ∏ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    unfold x, y, hr_to_NRpos, hr_to_NRneg.
    apply hr_to_NR_bij. }
  generalize (Cauchy_seq_impl_ex_lim_seq x (Cauchy_seq_pr1 u Cu)).
  set (lx := Cauchy_lim_seq x (Cauchy_seq_pr1 u Cu)) ; clearbody lx ; intro Hx.
  generalize (Cauchy_seq_impl_ex_lim_seq y (Cauchy_seq_pr2 u Cu)).
  set (ly := Cauchy_lim_seq y (Cauchy_seq_pr2 u Cu)) ; clearbody ly ; intro Hy.
  exists (NR_to_hr (lx,,ly)).
  intros c Hc.
  apply ispositive_halfNonnegativeReals in Hc.
  generalize (Hx _ Hc) (Hy _ Hc) ;
    apply hinhfun2 ; clear Hy Hx ;
    intros Nx Ny.
  exists (max (pr1 Nx) (pr1 Ny)) ; intros n Hn.
  rewrite <- Hxy ; simpl pr1.
  rewrite NR_to_hr_minus ; simpl.
  apply maxNonnegativeReals_lt.
  - rewrite hr_to_NRpos_NR_to_hr.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (y n + lx)).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus ; simpl.
    apply maxNonnegativeReals_lt.
    + rewrite (double_halfNonnegativeReals c), (iscomm_plusNonnegativeReals (y n)), (isassoc_plusNonnegativeReals lx (y n)), <- (isassoc_plusNonnegativeReals (y n)), (iscomm_plusNonnegativeReals (y n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (lx + _)).
      apply plusNonnegativeReals_ltcompat.
      apply (pr2 Nx).
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
      apply_pr2 (pr2 Ny).
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_halfNonnegativeReals.
  - rewrite hr_to_NRneg_NR_to_hr.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (x n + ly)).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus ; simpl.
    apply maxNonnegativeReals_lt.
    + rewrite (double_halfNonnegativeReals c), (iscomm_plusNonnegativeReals (x n)), (isassoc_plusNonnegativeReals ly (x n)), <- (isassoc_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (x n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (ly + _)).
      apply plusNonnegativeReals_ltcompat.
      apply (pr2 Ny).
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
      apply_pr2 (pr2 Nx).
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_halfNonnegativeReals.
Qed.

(** * Interface for Reals *)

Definition Reals : ConstructiveField := hr_ConstructiveField.

(** ** Operations and relations *)

Definition Rap : hrel Reals := CFap.
Definition Rlt : hrel Reals := hr_lt_rel.
Definition Rgt : hrel Reals := λ x y : Reals, Rlt y x.
Definition Rle : hrel Reals := hr_le_rel.
Definition Rge : hrel Reals := λ x y : Reals, Rle y x.

Definition Rzero : Reals := CFzero.
Definition Rplus : binop Reals := CFplus.
Definition Ropp : unop Reals := CFopp.
Definition Rminus : binop Reals := CFminus.

Definition Rone : Reals := CFone.
Definition Rmult : binop Reals := CFmult.
Definition Rinv : ∏ x : Reals, (Rap x Rzero) -> Reals := CFinv.
Definition Rdiv : Reals -> ∏ y : Reals, (Rap y Rzero) -> Reals := CFdiv.

Definition Rtwo : Reals := Rplus Rone Rone.
Definition Rabs : Reals → NonnegativeReals := hr_abs.

Definition NRNRtoR : NonnegativeReals → NonnegativeReals → Reals := λ (x y : NonnegativeReals), NR_to_hr (x,,y).
Definition RtoNRNR : Reals → NonnegativeReals × NonnegativeReals := λ x : Reals, (hr_to_NR x).

Declare Scope R_scope.
Delimit Scope R_scope with R.
Local Open Scope R_scope.

Infix "≠" := Rap : R_scope.
Infix "<" := Rlt : R_scope.
Infix ">" := Rgt : R_scope.
Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.

Notation "0" := Rzero : R_scope.
Notation "1" := Rone : R_scope.
Notation "2" := Rtwo : R_scope.
Infix "+" := Rplus : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "-" := Rminus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "/ x" := (Rinv (pr1 x) (pr2 x)) : R_scope.
Notation "x / y" := (Rdiv x (pr1 y) (pr2 y)) : R_scope.

(** ** NRNRtoR and RtoNRNR *)

Lemma NRNRtoR_RtoNRNR :
  ∏ x : Reals, NRNRtoR (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x)) = x.
Proof.
  intros X.
  unfold NRNRtoR.
  apply hr_to_NR_bij.
Qed.

Lemma RtoNRNR_NRNRtoR :
  ∏ x y : NonnegativeReals,
    (RtoNRNR (NRNRtoR x y)) = ((x - y)%NR ,, (y - x)%NR).
Proof.
  intros X Y.
  unfold RtoNRNR, NRNRtoR.
  unfold hr_to_NR, NR_to_hr.
  now rewrite setquotunivcomm.
Qed.

Lemma NRNRtoR_inside :
  ∏ x y : NonnegativeReals, pr1 (NRNRtoR x y) (x,,y).
Proof.
  intros x y.
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.

Lemma NRNRtoR_zero :
  NRNRtoR 0%NR 0%NR = 0.
Proof.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ 0 (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_one :
  NRNRtoR 1%NR 0%NR = 1.
Proof.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ 1 (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.

Lemma NRNRtoR_eq :
  ∏ x x' y y' : NonnegativeReals,
    (x + y' = x' + y)%NR <->
    NRNRtoR x y = NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply (NR_to_hr_eq (x,,y) (x' ,, y')).
Qed.
Lemma NRNRtoR_ap :
  ∏ x x' y y' : NonnegativeReals,
    (x + y' ≠ x' + y)%NR <->
    NRNRtoR x y ≠ NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply (NR_to_hr_ap (x,,y) (x' ,, y')).
Qed.
Lemma NRNRtoR_lt :
  ∏ x x' y y' : NonnegativeReals,
    (x + y' < x' + y)%NR <->
    NRNRtoR x y < NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply (NR_to_hr_lt (x,,y) (x' ,, y')).
Qed.
Lemma NRNRtoR_le :
  ∏ x x' y y' : NonnegativeReals,
    (x + y' <= x' + y)%NR <->
    NRNRtoR x y <= NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply (NR_to_hr_le (x,,y) (x' ,, y')).
Qed.

Lemma NRNRtoR_plus :
  ∏ x x' y y' : NonnegativeReals, NRNRtoR (x + x')%NR (y + y')%NR = NRNRtoR x y + NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply pathsinv0, NR_to_hr_plus.
Qed.
Lemma NRNRtoR_opp :
  ∏ x y : NonnegativeReals, NRNRtoR y x = - NRNRtoR x y.
Proof.
  intros x y.
  apply pathsinv0, NR_to_hr_opp.
Qed.
Lemma NRNRtoR_minus :
  ∏ x x' y y' : NonnegativeReals, NRNRtoR (x + y')%NR (y + x')%NR = NRNRtoR x y - NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply pathsinv0, NR_to_hr_minus.
Qed.
Lemma NRNRtoR_mult :
  ∏ x x' y y' : NonnegativeReals, NRNRtoR (x * x' + y * y')%NR (x * y' + y * x')%NR = NRNRtoR x y * NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  apply pathsinv0, NR_to_hr_mult.
Qed.
Lemma NRNRtoR_inv_pos :
  ∏ (x : NonnegativeReals) Hrn Hr,
    NRNRtoR (invNonnegativeReals x Hrn) 0%NR = Rinv (NRNRtoR x 0%NR) Hr.
Proof.
  intros x Hrn Hr.
  rewrite <- (isrunit_CFone_CFmult (NRNRtoR (invNonnegativeReals x Hrn) 0%NR)), <- (isrunit_CFone_CFmult (Rinv (NRNRtoR x 0%NR) Hr)).
  rewrite <- (isrinv_CFinv (X := Reals) (NRNRtoR x 0%NR) Hr).
  rewrite <- !(isassoc_CFmult (X := Reals)).
  apply (maponpaths (λ x, (x * _)%CF)).
  rewrite <- NRNRtoR_mult.
  unfold Rinv.
  rewrite (islinv_CFinv (X := Reals) (NRNRtoR x 0%NR) Hr).
  rewrite !israbsorb_zero_multNonnegativeReals, islabsorb_zero_multNonnegativeReals.
  rewrite !isrunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  apply NRNRtoR_one.
Qed.
Lemma NRNRtoR_inv_neg :
  ∏ (x : NonnegativeReals) Hrn Hr,
    NRNRtoR 0%NR (invNonnegativeReals x Hrn) = Rinv (NRNRtoR 0%NR x) Hr.
Proof.
  intros x Hrn Hr.
  rewrite <- (isrunit_CFone_CFmult (NRNRtoR 0%NR (invNonnegativeReals x Hrn))), <- (isrunit_CFone_CFmult (Rinv (NRNRtoR 0%NR x) Hr)).
  rewrite <- (isrinv_CFinv (X := Reals) (NRNRtoR 0%NR x) Hr).
  rewrite <- !(isassoc_CFmult (X := Reals)).
  apply (maponpaths (λ x, (x * _)%CF)).
  rewrite <- NRNRtoR_mult.
  unfold Rinv.
  rewrite (islinv_CFinv (X := Reals) (NRNRtoR 0%NR x) Hr).
  rewrite !israbsorb_zero_multNonnegativeReals, islabsorb_zero_multNonnegativeReals.
  rewrite !islunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  apply NRNRtoR_one.
Qed.

Lemma Rabs_pr1RtoNRNR :
  ∏ x : Reals,
    (pr1 (RtoNRNR x) <= Rabs x)%NR.
Proof.
  intros x.
  rewrite <- (NRNRtoR_RtoNRNR x).
  generalize (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x)) ; clear x ; intros x y ; simpl.
  apply maxNonnegativeReals_le_l.
Qed.
Lemma Rabs_pr2RtoNRNR :
  ∏ x : Reals,
    (pr2 (RtoNRNR x) <= Rabs x)%NR.
Proof.
  intros x.
  rewrite <- (NRNRtoR_RtoNRNR x).
  generalize (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x)) ; clear x ; intros x y ; simpl.
  apply maxNonnegativeReals_le_r.
Qed.

(** ** Theorems about apartness and order *)

Lemma ispositive_Rone : 0 < 1.
Proof.
  rewrite <- NRNRtoR_zero, <- NRNRtoR_one.
  apply NRNRtoR_lt.
  rewrite !isrunit_zero_plusNonnegativeReals.
  apply ispositive_apNonnegativeReals.
  apply isnonzeroNonnegativeReals.
Qed.

Lemma isirrefl_Rlt :
  ∏ x : Reals, ¬ (x < x).
Proof.
  exact (isirrefl_isStrongOrder (isStrongOrder_hr_lt)).
Qed.
Lemma istrans_Rlt :
  ∏ x y z : Reals, x < y -> y < z -> x < z.
Proof.
  exact (istrans_isStrongOrder (isStrongOrder_hr_lt)).
Qed.
Lemma iscotrans_Rlt :
  ∏ (x y z : Reals), (x < z) -> (x < y) ∨ (y < z).
Proof.
  exact iscotrans_hr_lt.
Qed.

Lemma Rplus_ltcompat_l:
  ∏ x y z : Reals, y < z <-> (y + x) < (z + x).
Proof.
  exact hr_plus_ltcompat_l.
Qed.
Lemma Rplus_ltcompat_r:
  ∏ x y z : Reals, y < z <-> (x + y) < (x + z).
Proof.
  exact hr_plus_ltcompat_r.
Qed.
Lemma Rmult_ltcompat_l:
  ∏ x y z : Reals,
    0 < x -> y < z -> (y * x) < (z * x).
Proof.
  exact hr_mult_ltcompat_l.
Qed.
Lemma Rmult_ltcompat_l':
  ∏ x y z : Reals,
    0 <= x -> (y * x) < (z * x) -> y < z.
Proof.
  exact hr_mult_ltcompat_l'.
Qed.
Lemma Rmult_ltcompat_r:
  ∏ x y z : Reals,
    0 < x -> y < z -> (x * y) < (x * z).
Proof.
  intros x y z.
  rewrite !(iscomm_CFmult x).
  now apply Rmult_ltcompat_l.
Qed.
Lemma Rmult_ltcompat_r':
  ∏ x y z : Reals,
    0 <= x -> (x * y) < (x * z) -> y < z.
Proof.
  exact hr_mult_ltcompat_r'.
Qed.

Lemma Rarchimedean:
  ∏ x : Reals, ∃ n : nat, x < nattoring n.
Proof.
  exact hr_archimedean.
Qed.

Lemma notRlt_Rle :
  ∏ x y : Reals, ¬ (x < y) <-> (y <= x).
Proof.
  exact hr_notlt_le.
Qed.
Lemma Rlt_Rle :
  ∏ x y : Reals, x < y -> x <= y.
Proof.
  intros x y H.
  apply notRlt_Rle.
  intros H0.
  refine (isirrefl_Rlt _ _).
  refine (istrans_Rlt _ _ _ _ _).
  exact H.
  exact H0.
Qed.
Lemma isantisymm_Rle :
  ∏ x y : Reals, x <= y -> y <= x -> x = y.
Proof.
  exact isantisymm_hr_le.
Qed.
Lemma istrans_Rle :
  ∏ x y z : Reals, x <= y -> y <= z -> x <= z.
Proof.
  intros x y z Hxy Hyz.
  apply notRlt_Rle ; intro H.
  generalize (iscotrans_Rlt _ y _ H).
  apply hinhuniv'.
  exact isapropempty.
  apply sumofmaps.
  + apply_pr2 notRlt_Rle.
    exact Hyz.
  + apply_pr2 notRlt_Rle.
    exact Hxy.
Qed.
Lemma istrans_Rle_lt :
  ∏ x y z : Reals, x <= y -> y < z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_Rlt _ x _ Hyz).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  apply fromempty.
  revert H.
  apply_pr2 notRlt_Rle.
  exact Hxy.
  exact H.
Qed.
Lemma istrans_Rlt_le :
  ∏ x y z : Reals, x < y -> y <= z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_Rlt _ z _ Hxy).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  exact H.
  apply fromempty.
  revert H.
  apply_pr2 notRlt_Rle.
  exact Hyz.
Qed.

Lemma Rplus_lecompat_l:
  ∏ x y z : Reals, y <= z <-> (y + x) <= (z + x).
Proof.
  exact hr_plus_lecompat_l.
Qed.
Lemma Rplus_lecompat_r:
  ∏ x y z : Reals, y <= z <-> (x + y) <= (x + z).
Proof.
  exact hr_plus_lecompat_r.
Qed.
Lemma Rmult_lecompat_l:
  ∏ x y z : Reals,
    0 <= x -> y <= z -> (y * x) <= (z * x).
Proof.
  exact hr_mult_lecompat_l.
Qed.
Lemma Rmult_lecompat_l':
  ∏ x y z : Reals,
    0 < x -> (y * x) <= (z * x) -> y <= z.
Proof.
  exact hr_mult_lecompat_l'.
Qed.
Lemma Rmult_lecompat_r:
  ∏ x y z : Reals,
    0 <= x -> y <= z -> (x * y) <= (x * z).
Proof.
  exact hr_mult_lecompat_r.
Qed.
Lemma Rmult_lecompat_r':
  ∏ x y z : Reals,
    0 < x -> (x * y) <= (x * z) -> y <= z.
Proof.
  exact hr_mult_lecompat_r'.
Qed.

Lemma Rap_Rlt:
  ∏ x y : Reals, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  exact hr_ap_lt.
Qed.

Lemma isnonzeroReals : (1 ≠ 0).
Proof.
  exact isnonzeroCF.
Qed.

Lemma isirrefl_Rap :
  ∏ x : Reals, ¬ (x ≠ x).
Proof.
  exact isirrefl_CFap.
Qed.
Lemma issymm_Rap :
  ∏ (x y : Reals), (x ≠ y) -> (y ≠ x).
Proof.
  exact issymm_CFap.
Qed.
Lemma iscotrans_Rap :
  ∏ (x y z : Reals), (x ≠ z) -> (x ≠ y) ∨ (y ≠ z).
Proof.
  exact iscotrans_CFap.
Qed.
Lemma istight_Rap :
  ∏ (x y : Reals), ¬ (x ≠ y) -> x = y.
Proof.
  exact istight_CFap.
Qed.

Lemma apRplus :
  ∏ (x x' y y' : Reals),
    (x + y ≠ x' + y') -> (x ≠ x') ∨ (y ≠ y').
Proof.
  exact apCFplus.
Qed.
Lemma Rplus_apcompat_l :
  ∏ x y z : Reals,
    y + x ≠ z + x <-> y ≠ z.
Proof.
  exact CFplus_apcompat_l.
Qed.
Lemma Rplus_apcompat_r :
  ∏ x y z : Reals,
    x + y ≠ x + z <-> y ≠ z.
Proof.
  exact CFplus_apcompat_r.
Qed.

Lemma apRmult:
  ∏ (x x' y y' : Reals),
  (x * y ≠ x' * y') -> (x ≠ x') ∨ (y ≠ y').
Proof.
  apply apCFmult.
Qed.
Lemma Rmult_apcompat_l:
  ∏ (x y z : Reals), (y * x ≠ z * x) -> (y ≠ z).
Proof.
  exact CFmult_apcompat_l.
Qed.
Lemma Rmult_apcompat_l':
  ∏ (x y z : Reals),
    (x ≠ 0) -> (y ≠ z) -> (y * x ≠ z * x).
Proof.
  exact CFmult_apcompat_l'.
Qed.
Lemma Rmult_apcompat_r:
  ∏ (x y z : Reals), (x * y ≠ x * z) -> (y ≠ z).
Proof.
  exact CFmult_apcompat_r.
Qed.
Lemma Rmult_apcompat_r':
  ∏ (x y z : Reals),
    (x ≠ 0) -> (y ≠ z) -> (x * y ≠ x * z).
Proof.
  exact CFmult_apcompat_r'.
Qed.
Lemma RmultapRzero:
  ∏ (x y : Reals),
    (x * y ≠ 0) -> (x ≠ 0) ∧ (y ≠ 0).
Proof.
  exact CFmultapCFzero.
Qed.

(** ** Algrebra *)

Lemma islunit_Rzero_Rplus :
  ∏ x : Reals, 0 + x = x.
Proof.
  exact islunit_CFzero_CFplus.
Qed.
Lemma isrunit_Rzero_Rplus :
  ∏ x : Reals, x + 0 = x.
Proof.
  exact isrunit_CFzero_CFplus.
Qed.
Lemma isassoc_Rplus :
  ∏ x y z : Reals, x + y + z = x + (y + z).
Proof.
  exact isassoc_CFplus.
Qed.
Lemma islinv_Ropp :
  ∏ x : Reals, - x + x = 0.
Proof.
  exact islinv_CFopp.
Qed.
Lemma isrinv_Ropp :
  ∏ x : Reals, x + - x = 0.
Proof.
  exact isrinv_CFopp.
Qed.

Lemma iscomm_Rplus :
  ∏ x y : Reals, x + y = y + x.
Proof.
  exact iscomm_CFplus.
Qed.
Lemma islunit_Rone_Rmult :
  ∏ x : Reals, 1 * x = x.
Proof.
  exact islunit_CFone_CFmult.
Qed.
Lemma isrunit_Rone_Rmult :
  ∏ x : Reals, x * 1 = x.
Proof.
  exact isrunit_CFone_CFmult.
Qed.
Lemma isassoc_Rmult :
  ∏ x y z : Reals, x * y * z = x * (y * z).
Proof.
  exact isassoc_CFmult.
Qed.
Lemma iscomm_Rmult :
  ∏ x y : Reals, x * y = y * x.
Proof.
  exact iscomm_CFmult.
Qed.
Lemma islinv_Rinv :
  ∏ (x : Reals) (Hx0 : x ≠ 0),
    (Rinv x Hx0) * x = 1.
Proof.
  exact islinv_CFinv.
Qed.
Lemma isrinv_Rinv :
  ∏ (x : Reals) (Hx0 : x ≠ 0),
    x * (Rinv x Hx0) = 1.
Proof.
  exact isrinv_CFinv.
Qed.
Lemma islabsorb_Rzero_Rmult :
  ∏ x : Reals, 0 * x = 0.
Proof.
  exact islabsorb_CFzero_CFmult.
Qed.
Lemma israbsorb_Rzero_Rmult :
  ∏ x : Reals, x * 0 = 0.
Proof.
  exact israbsorb_CFzero_CFmult.
Qed.
Lemma isldistr_Rplus_Rmult :
  ∏ x y z : Reals, z * (x + y) = z * x + z * y.
Proof.
  exact isldistr_CFplus_CFmult.
Qed.
Lemma isrdistr_Rplus_Rmult :
  ∏ x y z : Reals, (x + y) * z = x * z + y * z.
Proof.
  exact isrdistr_CFplus_CFmult.
Qed.

(** ** Rabs *)

Lemma istriangle_Rabs :
  ∏ x y : Reals, (Rabs (x + y)%R <= Rabs x + Rabs y)%NR.
Proof.
  exact istriangle_hr_abs.
Qed.
Lemma istriangle_Rabs' :
  ∏ x y : Reals, (Rabs x - Rabs y <= Rabs (x + y)%R)%NR.
Proof.
  exact istriangle_hr_abs'.
Qed.

Lemma Rabs_Rmult :
  ∏ x y : Reals, (Rabs (x * y)%R = Rabs x * Rabs y)%NR.
Proof.
  exact hr_abs_mult.
Qed.

Lemma Rabs_Ropp :
  ∏ x : Reals, (Rabs (- x)%R = Rabs x).
Proof.
  intros x.
  rewrite <- (NRNRtoR_RtoNRNR x).
  apply iscomm_maxNonnegativeReals.
Qed.
