(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Sets.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.NonnegativeReals.

Open Scope Dcuts_scope.

(** ** Definition *)

(** *** [commrng] *)

Definition hr_commrng : commrng := commrigtocommrng NonnegativeReals.

Definition NR_to_hr : NonnegativeReals × NonnegativeReals -> hr_commrng
  := setquotpr (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals)).

Lemma hr_to_NR (X : hr_commrng) :
  ∃ x : NonnegativeReals × NonnegativeReals, pr1 X x.
Proof.
  intros (X,(Hx,(Hx1,Hx2))) ; simpl.
  apply Hx.
Qed.

(** Caracterisation of equality *)

Lemma hr_inside_carac :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 X y -> pr1 x + pr2 y = pr1 y + pr2 x.
Proof.
  intros X x y Hx Hy.
  generalize (pr2 (pr2 (pr2 X)) _ _ Hx Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))).
  simpl ; intros (c,H).
  apply (plusNonnegativeReals_eqcompat_l c).
  exact H.
Qed.
Lemma hr_inside_carac' :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x -> pr1 X x -> pr1 X y.
Proof.
  intros X x y Heq Hx.
  apply (pr1 (pr2 (pr2 X)) x y).
  apply hinhpr.
  exists 0 ; simpl.
  change (pr1 x + pr2 y + 0 = pr1 y + pr2 x + 0).
  now rewrite !isrunit_zero_plusNonnegativeReals.
  exact Hx.
Qed.

Lemma hr_eq_carac :
  ∀ X Y : hr_commrng,
    X = Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y = pr1 y + pr2 x.
Proof.
  intros X Y ->.
  apply hr_inside_carac.
Qed.
Lemma hr_eq_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y = pr1 y + pr2 x -> X = Y.
Proof.
  intros X Y x y Hx Hy Heq.
  apply subtypeEquality.
  - intros Z.
    now apply isapropiseqclass.
  - apply funextfunax ; simpl ; intro t.
    apply weqtopathshProp, logeqweq.
    + intros Ht.
      revert Hy.
      apply hr_inside_carac'.
      apply plusNonnegativeReals_eqcompat_r with (pr2 x).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)), <- Heq, isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)), <-! isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_l.
      rewrite (iscomm_plusNonnegativeReals (pr2 x)).
      now apply (hr_inside_carac X).
    + intros Ht.
      revert Hx.
      apply hr_inside_carac'.
      apply plusNonnegativeReals_eqcompat_r with (pr2 y).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)), Heq, isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)), <-! isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_l.
      rewrite (iscomm_plusNonnegativeReals (pr2 y)).
      now apply (hr_inside_carac Y).
Qed.

Lemma NR_to_hr_unique :
  ∀ X : hr_commrng, ∀ x: NonnegativeReals × NonnegativeReals, pr1 X x -> NR_to_hr x = X.
Proof.
  intros X x Hx.
  apply (hr_eq_carac' _ _ x x).
  - apply hinhpr.
    now exists 0.
  - exact Hx.
  - reflexivity.
Qed.
Lemma hr_repres :
  ∀ X : hr_commrng, ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X (pr1 x - pr2 x,, pr2 x - pr1 x) <-> pr1 X x.
Proof.
  intros X x.
  split ; apply hr_inside_carac' ; simpl.
  - rewrite (iscomm_plusNonnegativeReals (pr1 x)).
    rewrite !Dcuts_minus_plus_max.
    apply iscomm_Dcuts_max.
  - rewrite (iscomm_plusNonnegativeReals (pr1 x)).
    rewrite !Dcuts_minus_plus_max.
    apply iscomm_Dcuts_max.
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
Definition hr_lt_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_ltNonnegativeReals.
Lemma hr_lt_carac :
  ∀ X Y : hr_commrng,
    hr_lt_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y < pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_lt_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_ltcompat_l c).
  exact Hlt.
Qed.
Lemma hr_lt_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y < pr1 y + pr2 x -> hr_lt_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_lt_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_ltcompat_l 0).
  exact Hlt.
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
Definition hr_le_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_leNonnegativeReals.
Lemma hr_le_carac :
  ∀ X Y : hr_commrng,
    hr_le_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y <= pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_le_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_lecompat_l c).
  exact Hlt.
Qed.
Lemma hr_le_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y <= pr1 y + pr2 x -> hr_le_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_le_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_lecompat_l 0).
  exact Hlt.
Qed.

(** Theorems about order *)

Lemma hr_notlt_le :
  ∀ X Y, ¬ hr_lt_rel X Y -> hr_le_rel Y X.
Proof.
  intros X Y Hlt.
  generalize (hr_to_NR X) (hr_to_NR Y) ;
    apply hinhuniv2 ; intros (x,Hx) (y,Hy).
  apply hr_le_carac' with y x.
  exact Hy.
  exact Hx.
  apply Dcuts_nlt_ge.
  intro H ; apply Hlt.
  now apply hr_lt_carac' with x y.
Qed.

Lemma isantisymm_hr_le :
  isantisymm hr_le_rel.
Proof.
  intros X Y Hxy Hyx.
  generalize (hr_to_NR X) (hr_to_NR Y) ;
    apply (hinhuniv2 (P := hProppair _ (pr2 (pr1 (pr1 (hr_commrng))) _ _))) ; intros (x,Hx) (y,Hy).
  apply hr_eq_carac' with x y.
  exact Hx.
  exact Hy.
  apply isantisym_leNonnegativeReals ; split.
  now apply hr_le_carac with X Y.
  now apply hr_le_carac with Y X.
Qed.

Lemma isStrongOrder_hr_lt : isStrongOrder hr_lt_rel.
Proof.
  split.
  - intros X Y Z Hxy Hyz.
    generalize (hr_to_NR X) (hr_to_NR Z) ;
      apply hinhuniv2 ; intros (x,Hx) (z,Hz).
    apply hr_lt_carac' with x z.
    exact Hx.
    exact Hz.
    generalize (hr_to_NR Y) ;
      apply hinhuniv ; intros (y,Hy).
    + apply_pr2 (plusNonnegativeReals_ltcompat_r (pr2 y)).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)).
      eapply istrans_ltNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_l.
      now apply hr_lt_carac with X Y.
      rewrite (iscomm_plusNonnegativeReals (pr1 y)), isassoc_plusNonnegativeReals, iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_l.
      rewrite (iscomm_plusNonnegativeReals (pr2 y)).
      now apply hr_lt_carac with Y Z.
  - intros X Hlt.
    generalize (hr_to_NR X) ; apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x,Hx).
    apply (isirrefl_ltNonnegativeReals (pr1 x + pr2 x)).
    now apply hr_lt_carac with X X.
Qed.
Lemma iscotrans_hr_lt :
  iscotrans hr_lt_rel.
Proof.
  intros X Y Z Hxz.
  generalize (hr_to_NR X) (hr_to_NR Z) ;
    apply hinhuniv2 ; intros (x,Hx) (z,Hz).
  generalize (hr_to_NR Y) ;
    apply hinhuniv ; intros (y,Hy).
  generalize (hr_lt_carac X Z Hxz x z Hx Hz) ; intro Hlt.
  apply (plusNonnegativeReals_ltcompat_r (pr2 y)) in Hlt.
  generalize (iscotrans_ltNonnegativeReals _ (pr1 y + pr2 x + pr2 z) _ Hlt).
  clear Hlt ; apply hinhfun ; intros [Hlt | Hlt].
  - left ; apply hr_lt_carac' with x y.
    exact Hx.
    exact Hy.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 z)).
    rewrite (iscomm_plusNonnegativeReals (pr1 x)), isassoc_plusNonnegativeReals.
    exact Hlt.
  - right ; apply hr_lt_carac' with y z.
    exact Hy.
    exact Hz.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 x)).
    rewrite isassoc_plusNonnegativeReals, <- (iscomm_plusNonnegativeReals (pr2 x)), (iscomm_plusNonnegativeReals (pr1 z)), isassoc_plusNonnegativeReals, <- isassoc_plusNonnegativeReals.
    exact Hlt.
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
Definition hr_ap_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_apNonnegativeReals.
Lemma hr_ap_carac :
  ∀ X Y : hr_commrng,
    hr_ap_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y ≠ pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_ap_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_apcompat_l c).
  exact Hlt.
Qed.
Lemma hr_ap_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y ≠ pr1 y + pr2 x -> hr_ap_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_ap_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_apcompat_l 0).
  exact Hlt.
Qed.

(** Theorems about apartness *)

Lemma hr_ap_lt :
  ∀ X Y : hr_commrng, hr_ap_rel X Y <-> hr_lt_rel X Y ∨ hr_lt_rel Y X.
Proof.
  intros X Y.
  split ; intro H.
  - generalize (hr_to_NR X) (hr_to_NR Y) ;
      apply hinhuniv2 ; intros (x,Hx) (y,Hy).
    generalize (hr_ap_carac _ _ H _ _ Hx Hy) ; clear H ; intro Hap.
    apply_pr2_in ap_ltNonnegativeReals Hap.
    revert Hap ; apply hinhfun ; intros [Hlt | Hlt].
    + now left ; apply hr_lt_carac' with x y.
    + now right ; apply hr_lt_carac' with y x.
  - generalize (hr_to_NR X) (hr_to_NR Y) ;
      apply hinhuniv2 ; intros (x,Hx) (y,Hy).
    apply hr_ap_carac' with x y.
    exact Hx.
    exact Hy.
    apply ap_ltNonnegativeReals.
    revert H ; apply hinhfun ; intros [Hlt | Hlt].
    + now left ; apply hr_lt_carac with X Y.
    + now right ; apply hr_lt_carac with Y X.
Qed.

Lemma istightap_hr_ap : istightap hr_ap_rel.
Proof.
  repeat split.
  - intros X Hap.
    generalize (hr_to_NR X) ;
      apply (hinhuniv (P := hProppair _ isapropempty)) ; intros (x,Hx).
    generalize (hr_ap_carac _ _ Hap _ _ Hx Hx).
    now apply isirrefl_apNonnegativeReals.
  - intros X Y Hap.
    generalize (hr_to_NR X) (hr_to_NR Y) ;
      apply hinhuniv2 ; intros (x,Hx) (y,Hy).
    apply hr_ap_carac' with y x.
    exact Hy.
    exact Hx.
    apply issymm_apNonnegativeReals.
    now apply hr_ap_carac with X Y.
  - intros X Y Z Hap.
    apply hr_ap_lt in Hap.
    revert Hap ; apply hinhuniv ; intros [Hlt|Hlt].
    + apply (iscotrans_hr_lt X Y Z) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * left ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; left.
      * right ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; left.
    + apply (iscotrans_hr_lt _ Y _) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * right ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; right.
      * left ; apply_pr2 hr_ap_lt.
        now apply hinhpr ; right.
  - intros X Y Hap.
    apply isantisymm_hr_le.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now apply hinhpr ; right.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now apply hinhpr ; left.
Qed.

(** Structures *)

Lemma hr_NR_ap_0 :
  ∀ (X : hr_commrng) (x : NonnegativeReals × NonnegativeReals),
    pr1 X x ->
    (hr_ap_rel X 0%rng <-> (pr2 x - pr1 x ≠ 0 ∨ pr1 x - pr2 x ≠ 0)).
Proof.
  intros X x Hx.
  split.
  - intros Hap.
    apply hr_ap_lt in Hap.
    revert Hap ; apply hinhfun ; intros [Hlt | Hlt].
    + left.
      apply (fun Hlt H0 => hr_lt_carac _ _ Hlt _ (0,,0) Hx H0) in Hlt ; simpl pr1 in Hlt ; simpl pr2 in Hlt.
      rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hlt.
      apply ap_ltNonnegativeReals, hinhpr.
      right.
      now apply ispositive_minusNonnegativeReals.
      now apply hinhpr ; exists 0 ; simpl.
    + right.
      apply (fun Hlt H0 => hr_lt_carac _ _ Hlt (0,,0) _ H0 Hx) in Hlt ; simpl pr1 in Hlt ; simpl pr2 in Hlt.
      rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hlt.
      apply ap_ltNonnegativeReals, hinhpr.
      right.
      now apply ispositive_minusNonnegativeReals.
      now apply hinhpr ; exists 0 ; simpl.
  - intro Hlt.
    apply (hr_ap_carac' _ _ x (0,,0) Hx).
    now apply hinhpr ; exists 0 ; simpl.
    simpl pr1 ; simpl pr2.
    rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
    apply ap_ltNonnegativeReals.
    revert Hlt ; apply hinhfun ; intros [Hap | Hap].
    + left.
      apply_pr2 ispositive_minusNonnegativeReals.
      apply_pr2_in ap_ltNonnegativeReals Hap.
      revert Hap ; apply hinhuniv ; intros [Hlt | Hlt].
      revert Hlt ; apply hinhuniv ; intros (c,(_,Hc)).
      now apply Dcuts_zero_empty in Hc.
      exact Hlt.
    + right.
      apply_pr2 ispositive_minusNonnegativeReals.
      apply_pr2_in ap_ltNonnegativeReals Hap.
      revert Hap ; apply hinhuniv ; intros [Hlt | Hlt].
      revert Hlt ; apply hinhuniv ; intros (c,(_,Hc)).
      now apply Dcuts_zero_empty in Hc.
      exact Hlt.
Qed.

Lemma islapbinop_plus : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z Hap.
  generalize (hr_to_NR X) ; apply hinhuniv ; intros (x,Hx).
  generalize (hr_to_NR Y) ; apply hinhuniv ; intros (y,Hy).
  generalize (hr_to_NR Z) ; apply hinhuniv ; intros (z,Hz).
  revert Hap.
  rewrite <- (NR_to_hr_unique _ _ Hx) ;
  rewrite <- (NR_to_hr_unique _ _ Hy) ;
  rewrite <- (NR_to_hr_unique _ _ Hz).
  simpl.
  apply hinhfun ; intros (c,Hap).
  exists c.
  change (pr1 y + pr2 z + c ≠ pr1 z + pr2 y + c).
  apply_pr2 (plusNonnegativeReals_apcompat_l (pr1 x + pr2 x)).
  cut (pr1 y + pr2 z + c + (pr1 x + pr2 x) = pr1 y + pr1 x + (pr2 z + pr2 x) + c).
  intros ->.
  cut (pr1 z + pr2 y + c + (pr1 x + pr2 x) = pr1 z + pr1 x + (pr2 y + pr2 x) + c).
  intros ->.
  exact Hap.
  - rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    apply iscomm_plusNonnegativeReals.
  - rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    apply iscomm_plusNonnegativeReals.
Qed.
Lemma israpbinop_plus : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z Hap.
  apply islapbinop_plus with X.
  rewrite !(rngcomm1 _ _ X).
  exact Hap.
Qed.
Lemma islapbinop_mult : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z Hap.
  generalize (hr_to_NR X) ; apply hinhuniv ; intros (x,Hx).
  generalize (hr_to_NR Y) ; apply hinhuniv ; intros (y,Hy).
  generalize (hr_to_NR Z) ; apply hinhuniv ; intros (z,Hz).
  revert Hap.
  rewrite <- (NR_to_hr_unique _ _ Hx) ;
  rewrite <- (NR_to_hr_unique _ _ Hy) ;
  rewrite <- (NR_to_hr_unique _ _ Hz).
  simpl.
  apply hinhfun ; intros (c,Hap).
  apply_pr2_in plusNonnegativeReals_apcompat_l Hap.
  exists 0.
  change (pr1 y + pr2 z + 0 ≠ pr1 z + pr2 y + 0).
  rewrite !isrunit_zero_plusNonnegativeReals.
  change (pr1 y * pr1 x + pr2 y * pr2 x + (pr1 z * pr2 x + pr2 z * pr1 x))%rng
  with (pr1 y * pr1 x + pr2 y * pr2 x + (pr1 z * pr2 x + pr2 z * pr1 x))
    in Hap.
  cut ((pr1 y * pr1 x + pr2 y * pr2 x + (pr1 z * pr2 x + pr2 z * pr1 x))
       = (pr1 y + pr2 z) * pr1 x + (pr2 y + pr1 z) * pr2 x).
  intro H ; rewrite H in Hap ; clear H.
  change (pr1 z * pr1 x + pr2 z * pr2 x + (pr1 y * pr2 x + pr2 y * pr1 x))%rng
  with (pr1 z * pr1 x + pr2 z * pr2 x + (pr1 y * pr2 x + pr2 y * pr1 x))
    in Hap.
  cut ((pr1 z * pr1 x + pr2 z * pr2 x + (pr1 y * pr2 x + pr2 y * pr1 x))
       = (pr1 z + pr2 y) * pr1 x + (pr2 z + pr1 y) * pr2 x).
  intro H ; rewrite H in Hap ; clear H.
  apply ap_plusNonnegativeReals in Hap.
  revert Hap ; apply hinhuniv ; intros [Hap | Hap].
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; intros [Hap | Hap].
    + exact Hap.
    + now apply fromempty, (isirrefl_apNonnegativeReals (pr1 x)), Hap .
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; intros [Hap | Hap].
    + rewrite (iscomm_plusNonnegativeReals (pr1 z)), iscomm_plusNonnegativeReals.
      now apply issymm_apNonnegativeReals, Hap.
    + now apply fromempty, (isirrefl_apNonnegativeReals (pr2 x)), Hap.
  - rewrite !isrdistr_plus_multNonnegativeReals.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    reflexivity.
  - rewrite !isrdistr_plus_multNonnegativeReals.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    reflexivity.
Qed.
Lemma israpbinop_mult : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z Hap.
  apply islapbinop_mult with X.
  rewrite !(rngcomm2 _ _ X).
  exact Hap.
Qed.

Lemma hr_ap_0_1 :
  isnonzeroCR hr_commrng (hr_ap_rel,, istightap_hr_ap).
Proof.
  apply hinhpr ; simpl pr1 ; simpl.
  exists 0 ; simpl.
  change (1 + 0 + 0 ≠ 0 + 0 + 0).
  rewrite !isrunit_zero_plusNonnegativeReals.
  apply isnonzeroNonnegativeReals.
Qed.

Lemma hr_islinv_neg :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (0%NR,, invNonnegativeReals x Hap) * NR_to_hr (0%NR,, x))%rng = 1%rng.
Proof.
  intros x Hap.
  apply hr_eq_carac' with ((1,,0) : NonnegativeReals × NonnegativeReals) ((1,,0) : NonnegativeReals × NonnegativeReals).
  - simpl ; apply hinhpr.
    exists 0.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
    now rewrite islinv_invNonnegativeReals.
  - apply hinhpr ; exists 0 ; simpl.
    reflexivity.
  - reflexivity.
Qed.
Lemma hr_isrinv_neg :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (0%NR,, x) * NR_to_hr (0%NR,, invNonnegativeReals x Hap))%rng = 1%rng.
Proof.
  intros x Hap.
  rewrite rngcomm2.
  now apply (hr_islinv_neg x Hap).
Qed.

Lemma hr_islinv_pos :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (invNonnegativeReals x Hap,,0%NR) * NR_to_hr (x,,0%NR))%rng = 1%rng.
Proof.
  intros x Hap.
  apply hr_eq_carac' with ((1,,0) : NonnegativeReals × NonnegativeReals) ((1,,0) : NonnegativeReals × NonnegativeReals).
  - simpl ; apply hinhpr.
    exists 0.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
    now rewrite islinv_invNonnegativeReals.
  - apply hinhpr ; exists 0 ; simpl.
    reflexivity.
  - reflexivity.
Qed.
Lemma hr_isrinv_pos :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (x,, 0%NR) * NR_to_hr (invNonnegativeReals x Hap,, 0%NR))%rng = 1%rng.
Proof.
  intros x Hap.
  rewrite rngcomm2.
  now apply (hr_islinv_pos x Hap).
Qed.

Lemma hr_ex_inv :
  ∀ x : hr_commrng,
    hr_ap_rel x 0%rng -> multinvpair hr_commrng x.
Proof.
  intros X Hap.
  generalize (hr_to_NR X).
  apply (hinhuniv (P := hProppair _ (isapropinvpair _ _))).
  intros x.
  apply (hr_NR_ap_0 _ _ (pr2 x)) in Hap.
  revert Hap ;
    apply hinhuniv ; intros [Hap|Hap] ; simpl.
  - set (Hx := pr2 (hr_repres X (pr1 x)) (pr2 x)) ; clearbody Hx.
    rewrite (minusNonnegativeReals_eq_zero (pr1 (pr1 x)) (pr2 (pr1 x))) in Hx.
    rewrite <- (NR_to_hr_unique _ _ Hx).
    eexists ; split.
    + now apply hr_islinv_neg.
    + exact (hr_isrinv_neg _ Hap).
    + apply Dcuts_lt_le_rel.
      apply_pr2 ispositive_minusNonnegativeReals.
      now apply ispositive_apNonnegativeReals.
  - set (Hx := pr2 (hr_repres X (pr1 x)) (pr2 x)) ; clearbody Hx.
    rewrite (minusNonnegativeReals_eq_zero (pr2 (pr1 x)) (pr1 (pr1 x))) in Hx.
    rewrite <- (NR_to_hr_unique _ _ Hx).
    eexists ; split.
    + now apply hr_islinv_pos.
    + exact (hr_isrinv_pos _ Hap).
    + apply Dcuts_lt_le_rel.
      apply_pr2 ispositive_minusNonnegativeReals.
      now apply ispositive_apNonnegativeReals.
Qed.

Definition hr_ConstructiveField : ConstructiveField.
Proof.
  exists hr_commrng.
  exists (_,,istightap_hr_ap).
  repeat split.
  - exact islapbinop_plus.
  - exact israpbinop_plus.
  - exact islapbinop_mult.
  - exact israpbinop_mult.
  - exact hr_ap_0_1.
  - exact hr_ex_inv.
Defined.