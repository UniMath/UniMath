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

Lemma hr_repres_pr1 :
  ∀ X : hr_commrng, ∀ x y : NonnegativeReals × NonnegativeReals, pr1 X x -> pr1 X y -> pr1 x - pr2 x <= pr1 y.
Proof.
  intros X x y Hx Hy.
  generalize (hr_inside_carac _ _ _ Hx Hy) ; intro Heq.
  apply_pr2 (plusNonnegativeReals_lecompat_l (pr2 x)).
  rewrite Dcuts_minus_plus_max.
  apply Dcuts_max_le.
  rewrite <- Heq.
  apply Dcuts_plus_le_l.
  apply Dcuts_plus_le_r.
Qed.
Lemma hr_repres_pr2 :
  ∀ X : hr_commrng, ∀ x y : NonnegativeReals × NonnegativeReals, pr1 X x -> pr1 X y -> pr2 x - pr1 x <= pr2 y.
Proof.
  intros X x y Hx Hy.
  generalize (hr_inside_carac _ _ _ Hx Hy) ; intro Heq.
  apply_pr2 (plusNonnegativeReals_lecompat_r (pr1 x)).
  rewrite iscomm_Dcuts_plus, Dcuts_minus_plus_max.
  apply Dcuts_max_le.
  rewrite Heq.
  apply Dcuts_plus_le_r.
  apply Dcuts_plus_le_l.
Qed.

Lemma isaprop_hr_to_NR (X : hr_commrng) :
  isaprop (Σ x : NonnegativeReals × NonnegativeReals,
                 pr1 X x × ∀ y : NonnegativeReals × NonnegativeReals, pr1 X y -> pr1 x <= pr1 y × pr2 x <= pr2 y).
Proof.
  intros X x x'.
  assert (Hp : ∀ x, isaprop (pr1 X x
       × (∀ y : NonnegativeReals × NonnegativeReals,
            pr1 X y -> pr1 x <= pr1 y × pr2 x <= pr2 y))).
  { clear ; intros x.
    apply isapropdirprod.
    apply pr2.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    apply isapropdirprod ; apply pr2. }
  assert (Heq : pr1 x = pr1 x').
  { clear.
    destruct x as ((x,y),(Hx,Hx')) ; simpl.
    destruct x' as ((x',y'),(Hy,Hy')) ; simpl.
    apply Utilities.simple_pair_path.
    apply isantisymm_leNonnegativeReals ; split.
    now apply (Hx' _ Hy).
    now apply (Hy' _ Hx).
    apply isantisymm_leNonnegativeReals ; split.
    now apply (pr2 (Hx' _ Hy)).
    now apply (pr2 (Hy' _ Hx)). }
  apply (iscontrweqb (X := (pr1 x = pr1 x'))).
  apply (total2_paths_hProp_equiv (λ x, hProppair _ (Hp x))).
  rewrite Heq.
  apply iscontrloopsifisaset.
  apply (isofhleveldirprod 2) ; apply pr2.
Qed.
Lemma hr_to_NR (X : hr_commrng) :
  Σ x : NonnegativeReals × NonnegativeReals,
        pr1 X x × ∀ y : NonnegativeReals × NonnegativeReals, pr1 X y -> pr1 x <= pr1 y × pr2 x <= pr2 y.
Proof.
  intros X.
  generalize (pr1 (pr2 X)) ;
  apply (hinhuniv (P := hProppair _ (isaprop_hr_to_NR X))) ; intros x.
  exists (pr1 (pr1 x) - pr2 (pr1 x) ,, pr2 (pr1 x) - pr1 (pr1 x)) ; split.
  - exact ((pr2 (hr_repres X (pr1 x))) (pr2 x)).
  - intros y Hy ; split.
    + refine (hr_repres_pr1 X _ _ (pr2 x) Hy).
    + refine (hr_repres_pr2 X _ _ (pr2 x) Hy).
Qed.

Lemma NR_to_hr_inside :
  ∀ x : NonnegativeReals × NonnegativeReals, pr1 (NR_to_hr x) x.
Proof.
  intros x.
  apply hinhpr ; simpl.
  exists 0 ; reflexivity.
Qed.

(** *** Constants and Operations *)

(** 0 *)

Lemma hr_zero_carac :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 (0%rng : hr_commrng) x -> pr2 x = pr1 x.
Proof.
  intros x.
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hx).
  apply (plusNonnegativeReals_eqcompat_r 0).
  apply (plusNonnegativeReals_eqcompat_l c).
  rewrite (iscomm_plusNonnegativeReals _ (pr1 x)).
  exact Hx.
Qed.
Lemma hr_zero_carac' :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr2 x = pr1 x -> pr1 (0%rng : hr_commrng) x.
Proof.
  intros x Hx.
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite iscomm_plusNonnegativeReals.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  exact Hx.
Qed.

(** 1 *)

Lemma hr_one_carac :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 (1%rng : hr_commrng) x -> 1 + pr2 x = pr1 x.
Proof.
  intros x.
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hx).
  rewrite isrunit_zero_plusNonnegativeReals in Hx.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hx.
Qed.
Lemma hr_one_carac' :
  ∀ x : NonnegativeReals × NonnegativeReals,
    1 + pr2 x = pr1 x -> pr1 (1%rng : hr_commrng) x.
Proof.
  intros x Hx.
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite isrunit_zero_plusNonnegativeReals.
  exact Hx.
Qed.

(** plus *)

Lemma hr_plus_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X + Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x + pr1 y + pr2 z = pr1 z + pr2 x + pr2 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_plus_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x + pr1 y + pr2 z = pr1 z + pr2 x + pr2 y ->
      pr1 (X + Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
Qed.

(** opp *)

Lemma hr_opp_carac :
  ∀ X : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (- X)%rng z ->
    ∀ x : NonnegativeReals × NonnegativeReals,
      pr1 X x ->
      pr2 x + pr2 z = pr1 z + pr1 x.
Proof.
  intros X z Hz x Hx.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_opp_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr2 x + pr2 z = pr1 z + pr1 x ->
      pr1 (- X)%rng z.
Proof.
  intros X x Hx z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  exact Hz.
Qed.

(** minus *)

Lemma hr_minus_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X - Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x + pr2 y + pr2 z = pr1 z + pr2 x + pr1 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_minus_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x + pr2 y + pr2 z = pr1 z + pr2 x + pr1 y ->
      pr1 (X - Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
Qed.

(** mult *)

Lemma hr_mult_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X * Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x * pr1 y + pr2 x * pr2 y + pr2 z = pr1 z + pr1 x * pr2 y + pr2 x * pr1 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_mult_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x * pr1 y + pr2 x * pr2 y + pr2 z = pr1 z + pr1 x * pr2 y + pr2 x * pr1 y ->
      pr1 (X * Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
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
  ∀ X Y, ¬ hr_lt_rel X Y <-> hr_le_rel Y X.
Proof.
  intros X Y.
  destruct (hr_to_NR X) as (x,(Hx,_)).
  destruct (hr_to_NR Y) as (y,(Hy,_)).
  split ; intro H.
  - apply hr_le_carac' with y x.
    exact Hy.
    exact Hx.
    apply Dcuts_nlt_ge.
    intro H0 ; apply H.
    now apply hr_lt_carac' with x y.
  - intro H0.
    generalize (hr_lt_carac _ _ H0 _ _ Hx Hy).
    apply_pr2 Dcuts_nlt_ge.
    apply hr_le_carac with Y X.
    exact H.
    exact Hy.
    exact Hx.
Qed.

Lemma isantisymm_hr_le :
  isantisymm hr_le_rel.
Proof.
  intros X Y Hxy Hyx.
  generalize (hr_to_NR X) (hr_to_NR Y) ;
    intros (x,(Hx,_)) (y,(Hy,_)).
  apply hr_eq_carac' with x y.
  exact Hx.
  exact Hy.
  apply isantisymm_leNonnegativeReals ; split.
  now apply hr_le_carac with X Y.
  now apply hr_le_carac with Y X.
Qed.

Lemma isStrongOrder_hr_lt : isStrongOrder hr_lt_rel.
Proof.
  split.
  - intros X Y Z Hxy Hyz.
    generalize (hr_to_NR X) (hr_to_NR Y) (hr_to_NR Z) ;
      intros (x,(Hx,_)) (y,(Hy,_)) (z,(Hz,_)).
    apply hr_lt_carac' with x z.
    exact Hx.
    exact Hz.
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
    generalize (hr_to_NR X) ; intros (x,(Hx,_)).
    apply (isirrefl_ltNonnegativeReals (pr1 x + pr2 x)).
    now apply hr_lt_carac with X X.
Qed.
Lemma iscotrans_hr_lt :
  iscotrans hr_lt_rel.
Proof.
  intros X Y Z Hxz.
  generalize (hr_to_NR X) (hr_to_NR Y) (hr_to_NR Z) ;
    intros (x,(Hx,_)) (y,(Hy,_)) (z,(Hz,_)).
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

Lemma hr_ispositive_carac :
  ∀ X : hr_commrng,
    hr_lt_rel 0%rng X ->
    Σ x : NonnegativeReals, pr1 X (x ,, 0) × 0 < x.
Proof.
  intros X Hlt.
  destruct (hr_to_NR X) as (x,(Hx, Hmin)).
  eapply hr_lt_carac in Hlt.
  2: now apply (hr_zero_carac' (0,,0)).
  2: exact Hx.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hlt.
  exists (pr1 x) ; split.
  generalize Hx ; apply hr_inside_carac' ; simpl.
  apply_pr2 plusNonnegativeReals_eqcompat_r.
  apply pathsinv0, le0_NonnegativeReals.
  eapply istrans_leNonnegativeReals.
  apply_pr2 (Hmin (pr1 x - pr2 x ,, pr2 x - pr1 x)).
  apply_pr2 hr_repres.
  exact Hx.
  simpl pr2.
  apply_pr2 le0_NonnegativeReals.
  apply minusNonnegativeReals_eq_zero.
  apply Dcuts_lt_le_rel.
  exact Hlt.
  eapply istrans_le_lt_ltNonnegativeReals, Hlt.
  apply isnonnegative_NonnegativeReals.
Qed.
Lemma hr_ispositive_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr2 x < pr1 x ->
    hr_lt_rel 0%rng X.
Proof.
  intros X x Hx Hlt.
  eapply hr_lt_carac'.
  now apply (hr_zero_carac' (0,,0)).
  exact Hx.
  rewrite islunit_zero_plusNonnegativeReals,  isrunit_zero_plusNonnegativeReals.
  exact Hlt.
Qed.

Lemma hr_isnonnegative_carac :
  ∀ X : hr_commrng,
    hr_le_rel 0%rng X ->
    Σ x : NonnegativeReals, pr1 X (x ,, 0).
Proof.
  intros X Hle.
  destruct (hr_to_NR X) as (x,(Hx, Hmin)).
  eapply hr_le_carac in Hle.
  2: now apply (hr_zero_carac' (0,,0)).
  2: exact Hx.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hle.
  exists (pr1 x).
  generalize Hx ; apply hr_inside_carac' ; simpl.
  apply_pr2 plusNonnegativeReals_eqcompat_r.
  apply pathsinv0, le0_NonnegativeReals.
  eapply istrans_leNonnegativeReals.
  apply_pr2 (Hmin (pr1 x - pr2 x ,, pr2 x - pr1 x)).
  apply_pr2 hr_repres.
  exact Hx.
  simpl pr2.
  apply_pr2 le0_NonnegativeReals.
  apply minusNonnegativeReals_eq_zero.
  exact Hle.
Qed.
Lemma hr_isnonnegative_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr2 x <= pr1 x ->
    hr_le_rel 0%rng X.
Proof.
  intros X x Hx Hle.
  eapply hr_le_carac'.
  now apply (hr_zero_carac' (0,,0)).
  exact Hx.
  rewrite islunit_zero_plusNonnegativeReals,  isrunit_zero_plusNonnegativeReals.
  exact Hle.
Qed.

Lemma hr_isnegative_carac :
  ∀ X : hr_commrng,
    hr_lt_rel X 0%rng ->
    Σ x : NonnegativeReals, pr1 X (0 ,, x) × 0 < x.
Proof.
  intros X Hlt.
  destruct (hr_to_NR X) as (x,(Hx, Hmin)).
  eapply hr_lt_carac in Hlt.
  2: exact Hx.
  2: now apply (hr_zero_carac' (0,,0)).
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hlt.
  exists (pr2 x) ; split.
  generalize Hx ; apply hr_inside_carac' ; simpl.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  apply le0_NonnegativeReals.
  eapply istrans_leNonnegativeReals.
  apply (Hmin (pr1 x - pr2 x ,, pr2 x - pr1 x)).
  apply_pr2 hr_repres.
  exact Hx.
  simpl pr1.
  apply_pr2 le0_NonnegativeReals.
  apply minusNonnegativeReals_eq_zero.
  apply Dcuts_lt_le_rel.
  exact Hlt.
  eapply istrans_le_lt_ltNonnegativeReals, Hlt.
  apply isnonnegative_NonnegativeReals.
Qed.
Lemma hr_isnegative_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr1 x < pr2 x ->
    hr_lt_rel X 0%rng.
Proof.
  intros X x Hx Hlt.
  eapply hr_lt_carac'.
  exact Hx.
  now apply (hr_zero_carac' (0,,0)).
  rewrite islunit_zero_plusNonnegativeReals,  isrunit_zero_plusNonnegativeReals.
  exact Hlt.
Qed.

Lemma hr_isnonpositive_carac :
  ∀ X : hr_commrng,
    hr_le_rel X 0%rng ->
    Σ x : NonnegativeReals, pr1 X (0 ,, x).
Proof.
  intros X Hle.
  destruct (hr_to_NR X) as (x,(Hx, Hmin)).
  eapply hr_le_carac in Hle.
  2: exact Hx.
  2: now apply (hr_zero_carac' (0,,0)).
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals in Hle.
  exists (pr2 x).
  generalize Hx ; apply hr_inside_carac' ; simpl.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  apply le0_NonnegativeReals.
  eapply istrans_leNonnegativeReals.
  apply (Hmin (pr1 x - pr2 x ,, pr2 x - pr1 x)).
  apply_pr2 hr_repres.
  exact Hx.
  simpl pr1.
  apply_pr2 le0_NonnegativeReals.
  apply minusNonnegativeReals_eq_zero.
  exact Hle.
Qed.
Lemma hr_isnonpositive_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr1 x <= pr2 x ->
    hr_le_rel X 0%rng.
Proof.
  intros X x Hx Hle.
  eapply hr_le_carac'.
  exact Hx.
  now apply (hr_zero_carac' (0,,0)).
  rewrite islunit_zero_plusNonnegativeReals,  isrunit_zero_plusNonnegativeReals.
  exact Hle.
Qed.

Lemma hr_plus_ltcompat_l :
  ∀ x y z : hr_commrng, hr_lt_rel y z <-> hr_lt_rel (y+x)%rng (z+x)%rng.
Proof.
  intros X Y Z.
  destruct (hr_to_NR X) as (x,(Hx,_)).
  destruct (hr_to_NR Y) as (y,(Hy,_)).
  destruct (hr_to_NR Z) as (z,(Hz,_)).
  split ; intro Hlt.
  - eapply hr_lt_carac'.
    + eapply hr_plus_carac'.
      exact Hy.
      exact Hx.
      instantiate (1 := (pr1 y + pr1 x ,, pr2 y + pr2 x)).
      simpl ; rewrite <- ! isassoc_plusNonnegativeReals.
      reflexivity.
    + eapply hr_plus_carac'.
      exact Hz.
      exact Hx.
      instantiate (1 := (pr1 z + pr1 x ,, pr2 z + pr2 x)).
      simpl ; rewrite <- ! isassoc_plusNonnegativeReals.
      reflexivity.
    + simpl pr1 ; simpl pr2.
      rewrite !(iscomm_plusNonnegativeReals _ (pr1 x)), !isassoc_plusNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_r.
      rewrite <- ! isassoc_plusNonnegativeReals.
      apply plusNonnegativeReals_ltcompat_l.
      refine (hr_lt_carac Y Z Hlt _ _ Hy Hz).
  - refine (hr_lt_carac' _ _ y z Hy Hz _).
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 x)).
    apply_pr2 (plusNonnegativeReals_ltcompat_r (pr1 x)).
    rewrite <- ! isassoc_plusNonnegativeReals.
    rewrite !(iscomm_plusNonnegativeReals (pr1 x)), !(isassoc_plusNonnegativeReals (_ + pr1 x)).
    refine (hr_lt_carac _ _ Hlt (pr1 y + pr1 x ,, pr2 y + pr2 x) (pr1 z + pr1 x ,, pr2 z + pr2 x) _ _).
    + eapply hr_plus_carac'.
      exact Hy.
      exact Hx.
      simpl ; rewrite <- ! isassoc_plusNonnegativeReals.
      reflexivity.
    + eapply hr_plus_carac'.
      exact Hz.
      exact Hx.
      simpl ; rewrite <- ! isassoc_plusNonnegativeReals.
      reflexivity.
Qed.
Lemma hr_plus_ltcompat_r :
  ∀ x y z : hr_commrng, hr_lt_rel y z <-> hr_lt_rel (x + y)%rng (x + z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm1 _ x).
  apply hr_plus_ltcompat_l.
Qed.

Lemma hr_plus_lecompat_l :
  ∀ x y z : hr_commrng, hr_le_rel y z <-> hr_le_rel (y + x)%rng (z + x)%rng.
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
  ∀ x y z : hr_commrng, hr_le_rel y z <-> hr_le_rel (x + y)%rng (x + z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm1 _ x).
  apply hr_plus_lecompat_l.
Qed.

Lemma hr_mult_ltcompat_l :
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_lt_rel y z -> hr_lt_rel (y * x)%rng (z * x)%rng.
Proof.
  intros X Y Z Hx0 Hlt.
  destruct (hr_to_NR Y) as (y,(Hy,_)).
  destruct (hr_to_NR Z) as (z,(Hz,_)).
  eapply hr_ispositive_carac in Hx0.
  destruct Hx0 as (x,(Hx,Hx0)).
  eapply hr_lt_carac in Hlt.
  2: exact Hy.
  2: exact Hz.
  eapply hr_lt_carac'.
  - eapply hr_mult_carac'.
    exact Hy.
    exact Hx.
    instantiate (1 := (pr1 y * x ,, pr2 y * x)).
    simpl ; rewrite !israbsorb_zero_multNonnegativeReals, isrunit_zero_plusNonnegativeReals.
    reflexivity.
  - eapply hr_mult_carac'.
    exact Hz.
    exact Hx.
    instantiate (1 := (pr1 z * x ,, pr2 z * x)).
    simpl ; rewrite !israbsorb_zero_multNonnegativeReals, isrunit_zero_plusNonnegativeReals.
    reflexivity.
  - simpl pr1 ; simpl pr2.
    rewrite <- !isrdistr_plus_multNonnegativeReals.
    apply multNonnegativeReals_ltcompat_l.
    exact Hx0.
    exact Hlt.
Qed.
Lemma hr_mult_ltcompat_l' :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_lt_rel (y * x)%rng (z * x)%rng -> hr_lt_rel y z.
Proof.
  intros X Y Z Hx0 Hlt.
  apply hr_isnonnegative_carac in Hx0.
  destruct Hx0 as (x,Hx).
  destruct (hr_to_NR Y) as (y,(Hy,_)).
  destruct (hr_to_NR Z) as (z,(Hz,_)).
  refine (hr_lt_carac' _ _ y z Hy Hz _).
  eapply hr_lt_carac in Hlt.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hy.
  exact Hx.
  instantiate (1 := (pr1 y * x ,, pr2 y * x)).
  simpl ; rewrite !israbsorb_zero_multNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  reflexivity.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hz.
  exact Hx.
  instantiate (1 := (pr1 z * x ,, pr2 z * x)).
  simpl ; rewrite !israbsorb_zero_multNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  reflexivity.

  simpl pr1 in Hlt ; simpl pr2 in Hlt.
  rewrite <- !isrdistr_plus_multNonnegativeReals in Hlt.
  apply multNonnegativeReals_ltcompat_l' with x.
  exact Hlt.
Qed.
Lemma hr_mult_ltcompat_r' :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_lt_rel (x * y)%rng (x * z)%rng -> hr_lt_rel y z.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
  apply hr_mult_ltcompat_l'.
Qed.

Lemma hr_mult_lecompat_l :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_le_rel y z -> hr_le_rel (y * x)%rng (z * x)%rng.
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
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_le_rel (y * x)%rng (z * x)%rng -> hr_le_rel y z.
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
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_le_rel y z -> hr_le_rel (x * y)%rng (x * z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
  apply hr_mult_lecompat_l.
Qed.
Lemma hr_mult_lecompat_r' :
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_le_rel (x * y)%rng (x * z)%rng -> hr_le_rel y z.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
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
      intros (x,(Hx,_)) (y,(Hy,_)).
    generalize (hr_ap_carac _ _ H _ _ Hx Hy) ; clear H ; intro Hap.
    apply_pr2_in ap_ltNonnegativeReals Hap.
    revert Hap ; apply hinhfun ; intros [Hlt | Hlt].
    + now left ; apply hr_lt_carac' with x y.
    + now right ; apply hr_lt_carac' with y x.
  - generalize (hr_to_NR X) (hr_to_NR Y) ;
      intros (x,(Hx,_)) (y,(Hy,_)).
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
    generalize (hr_to_NR X) ; intros (x,(Hx,_)).
    generalize (hr_ap_carac _ _ Hap _ _ Hx Hx).
    now apply isirrefl_apNonnegativeReals.
  - intros X Y Hap.
    generalize (hr_to_NR X) (hr_to_NR Y) ;
      intros (x,(Hx,_)) (y,(Hy,_)).
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
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  intro Hap.
  apply_pr2 hr_ap_lt.
  apply hr_ap_lt in Hap.
  revert Hap ; apply hinhfun ; intros [Hlt | Hlt].
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
  rewrite !(rngcomm1 _ _ X).
  exact Hap.
Qed.

Lemma islapbinop_mult : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  intro Hap.
  generalize (hr_to_NR X) (hr_to_NR Y) (hr_to_NR Z) ; intros (x,(Hx,_)) (y,(Hy,_)) (z,(Hz,_)).
  eapply hr_ap_carac in Hap.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hy.
  exact Hx.
  instantiate (1 := (pr1 y * pr1 x + pr2 y * pr2 x ,, pr1 y * pr2 x + pr2 y * pr1 x)).
  simpl pr1 ; simpl pr2 ; rewrite !isassoc_plusNonnegativeReals.
  reflexivity.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hz.
  exact Hx.
  instantiate (1 := (pr1 z * pr1 x + pr2 z * pr2 x ,, pr1 z * pr2 x + pr2 z * pr1 x)).
  simpl pr1 ; simpl pr2 ; rewrite !isassoc_plusNonnegativeReals.
  reflexivity.
  simpl pr1 in Hap ; simpl pr2 in Hap.
  eapply hr_ap_carac'.
  exact Hy.
  exact Hz.
  cut ((pr1 y * pr1 x + pr2 y * pr2 x + (pr1 z * pr2 x + pr2 z * pr1 x))
       = (pr1 y + pr2 z) * pr1 x + (pr2 y + pr1 z) * pr2 x).
  intro H ; simpl in Hap,H ; rewrite H in Hap ; clear H.
  cut ((pr1 z * pr1 x + pr2 z * pr2 x + (pr1 y * pr2 x + pr2 y * pr1 x))
       = (pr1 z + pr2 y) * pr1 x + (pr2 z + pr1 y) * pr2 x).
  intro H ; simpl in H,Hap ; rewrite H in Hap ; clear H.
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
  eapply hr_eq_carac'.
  - eapply hr_mult_carac'.
    now apply NR_to_hr_inside.
    now apply NR_to_hr_inside.
    simpl pr1 ; simpl pr2.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
    rewrite islinv_invNonnegativeReals.
    apply hr_one_carac.
    now apply NR_to_hr_inside.
  - now apply NR_to_hr_inside.
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
  eapply hr_eq_carac'.
  - eapply hr_mult_carac'.
    now apply NR_to_hr_inside.
    now apply NR_to_hr_inside.
    simpl pr1 ; simpl pr2.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
    rewrite islinv_invNonnegativeReals.
    apply hr_one_carac.
    now apply NR_to_hr_inside.
  - now apply NR_to_hr_inside.
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
  apply hr_ap_lt in Hap.
  revert Hap ;
    apply (hinhuniv (P := hProppair _ (isapropinvpair _ _))) ; intros [Hlt|Hlt] ; simpl.
  - apply hr_isnegative_carac in Hlt.
    destruct Hlt as (x,(Hx,Hap)).
    apply_pr2_in ispositive_apNonnegativeReals Hap.
    rewrite <- (NR_to_hr_unique _ _ Hx).
    eexists ; split.
    + now apply hr_islinv_neg.
    + exact (hr_isrinv_neg _ Hap).
  - apply hr_ispositive_carac in Hlt.
    destruct Hlt as (x,(Hx,Hap)).
    apply_pr2_in ispositive_apNonnegativeReals Hap.
    rewrite <- (NR_to_hr_unique _ _ Hx).
    eexists ; split.
    + now apply hr_islinv_pos.
    + exact (hr_isrinv_pos _ Hap).
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

(** ** hr_abs *)

Definition hr_abs (x : hr_ConstructiveField) : NonnegativeReals :=
  maxNonnegativeReals (pr1 (pr1 (hr_to_NR x))) (pr2 (pr1 (hr_to_NR x))).

Lemma hr_abs_pty1 :
  ∀ X : hr_ConstructiveField,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x -> (hr_abs X <= maxNonnegativeReals (pr1 x) (pr2 x)).
Proof.
  intros X x Hx.
  unfold hr_abs.
  destruct (hr_to_NR X) as (y,(Hy,Hle)).
  simpl pr1.
  apply Dcuts_max_le.
  - apply istrans_leNonnegativeReals with (pr1 x).
    now apply Hle.
    apply Dcuts_max_le_l.
  - apply istrans_leNonnegativeReals with (pr2 x).
    apply (pr2 (Hle _ Hx)).
    apply Dcuts_max_le_r.
Qed.
Lemma hr_abs_opp :
  ∀ x : hr_ConstructiveField, hr_abs (- x)%rng = hr_abs x.
Proof.
  intros X.
  apply isantisymm_leNonnegativeReals ; split.
  - apply Dcuts_max_le.
    + eapply istrans_leNonnegativeReals, Dcuts_max_le_r.
      apply (pr2 (pr2 (hr_to_NR (- X)%rng)) (pr2 (pr1 (hr_to_NR X)),,pr1 (pr1 (hr_to_NR X)))).
      destruct (hr_to_NR X) as (x,(Hx,Hx')) ; simpl pr1.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
    + eapply istrans_leNonnegativeReals, Dcuts_max_le_l.
      apply (fun H => pr2 ((pr2 (pr2 (hr_to_NR (- X)%rng)) (pr2 (pr1 (hr_to_NR X)),,pr1 (pr1 (hr_to_NR X)))) H)).
      destruct (hr_to_NR X) as (x,(Hx,Hx')) ; simpl pr1.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
  - apply Dcuts_max_le.
    + eapply istrans_leNonnegativeReals, Dcuts_max_le_r.
      apply (pr2 (pr2 (hr_to_NR (X))) (pr2 (pr1 (hr_to_NR (- X)%rng)),,pr1 (pr1 (hr_to_NR (-X)%rng)))).
      destruct (hr_to_NR (- X)%rng) as (x,(Hx,Hx')) ; simpl pr1.
      assert (X = (- - X)%rng).
      { apply pathsinv0, rngminusminus. }
      rewrite X0.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
    + eapply istrans_leNonnegativeReals, Dcuts_max_le_l.
      apply (fun H => pr2 ((pr2 (pr2 (hr_to_NR (X))) (pr2 (pr1 (hr_to_NR (- X)%rng)),,pr1 (pr1 (hr_to_NR (-X)%rng)))) H) ).
      destruct (hr_to_NR (- X)%rng) as (x,(Hx,Hx')) ; simpl pr1.
      assert (X = (- - X)%rng).
      { apply pathsinv0, rngminusminus. }
      rewrite X0.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
Qed.

(** ** Completeness *)

Definition Cauchy_seq (u : nat -> hr_ConstructiveField) : hProp.
Proof.
  intro u.
  apply (hProppair (∀ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∀ n m : nat, N ≤ n -> N ≤ m -> hr_abs (u m - u n)%rng < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.

Lemma Cauchy_seq_pr1 (u : nat -> hr_ConstructiveField) :
  let x := λ n : nat, pr1 (pr1 (hr_to_NR (u n))) in
  Cauchy_seq u -> NonnegativeReals.Cauchy_seq x.
Proof.
  intros u x.
  set (y := λ n : nat, pr2 (pr1 (hr_to_NR (u n)))) ; simpl in y.
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros (N,Hu).
  exists N ; intros n m Hn Hm.
  specialize (Hu _ _ Hn Hm).
  split.
  - apply (plusNonnegativeReals_ltcompat_r (x m)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (x m + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply Dcuts_max_le_r.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    eapply (hr_minus_carac (u m) (u n)) in Hz.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    simpl in Hz.
    apply ((pr2 (pr2 (hr_to_NR (u n)))) (x m + pr2 z ,, y m + pr1 z)).
    generalize (pr1 (pr2 (hr_to_NR (u n)))).
    apply hr_inside_carac' ; simpl pr1 ; simpl pr2.
    rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (y m + x n)), <-isassoc_plusNonnegativeReals.
    rewrite <- Hz.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    apply iscomm_plusNonnegativeReals.
  - apply (plusNonnegativeReals_ltcompat_r (x n)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (x n + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply Dcuts_max_le_l.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    eapply (hr_minus_carac (u m) (u n)) in Hz.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    simpl in Hz.
    apply ((pr2 (pr2 (hr_to_NR (u m)))) (x n + pr1 z ,, y n + pr2 z)).
    generalize (pr1 (pr2 (hr_to_NR (u m)))).
    apply hr_inside_carac'.
    simpl pr1 ; simpl pr2.
    rewrite <- !isassoc_plusNonnegativeReals.
    change (pr1 (pr1 (hr_to_NR (u m)))) with (x m).
    rewrite Hz.
    rewrite iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals.
    reflexivity.
Qed.
Lemma Cauchy_seq_pr2 (u : nat -> hr_ConstructiveField) :
  let y := λ n : nat, pr2 (pr1 (hr_to_NR (u n))) in
  Cauchy_seq u -> NonnegativeReals.Cauchy_seq y.
Proof.
  intros u y ; simpl in y.
  set (x := λ n : nat, pr1 (pr1 (hr_to_NR (u n)))).
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros (N,Hu).
  exists N ; intros n m Hn Hm.
  specialize (Hu _ _ Hn Hm).
  split.
  - apply (plusNonnegativeReals_ltcompat_r (y m)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (y m + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply Dcuts_max_le_l.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    revert Hz.
    rewrite <- ! Hxy ; apply hinhuniv ; intros (d,Hd) ;
    simpl in Hd.
    apply (fun H => pr2 (((pr2 (pr2 (hr_to_NR (u n)))) (x m + pr2 z ,, y m + pr1 z)) H)).
    rewrite <- Hxy ; apply hinhpr ; simpl.
    exists d.
    rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (y m + x n)).
    change ((pr1 z + (y m + x n))%NR + d)%rng
    with (pr1 z + (y m + x n) + d)%rng.
    simpl in Hd |- * ; rewrite <- Hd.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    rewrite <- !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    apply iscomm_plusNonnegativeReals.
  - apply (plusNonnegativeReals_ltcompat_r (y n)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (y n + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply Dcuts_max_le_r.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    revert Hz.
    rewrite <- ! Hxy ; apply hinhuniv ; intros (d,Hd) ;
    simpl in Hd.
    apply (fun H => pr2 (((pr2 (pr2 (hr_to_NR (u m)))) (x n + pr1 z ,, y n + pr2 z)) H)).
    rewrite <- Hxy ; apply hinhpr ; simpl.
    exists d.
    rewrite <- !isassoc_plusNonnegativeReals.
    change ((x m + y n + pr2 z)%NR + d)%rng
    with (x m + y n + pr2 z + d)%rng.
    simpl in Hd |- * ; rewrite Hd.
    rewrite <- !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    now rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
Qed.

Definition is_lim_seq (u : nat -> hr_ConstructiveField) (l : hr_ConstructiveField) : hProp.
Proof.
  intros u l.
  apply (hProppair (∀ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∀ n : nat, N ≤ n -> hr_abs (u n - l)%rng < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.
Definition ex_lim_seq (u : nat -> hr_ConstructiveField) := Σ l, is_lim_seq u l.

Lemma Cauchy_seq_impl_ex_lim_seq (u : nat -> hr_ConstructiveField) :
  Cauchy_seq u -> ex_lim_seq u.
Proof.
  intros u Cu.
  set (x := λ n, pr1 (pr1 (hr_to_NR (u n)))).
  set (y := λ n, pr2 (pr1 (hr_to_NR (u n)))) ; simpl in y.
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  generalize (Cauchy_seq_impl_ex_lim_seq x (Cauchy_seq_pr1 u Cu)).
  set (lx := Cauchy_lim_seq x (Cauchy_seq_pr1 u Cu)) ; clearbody lx ; intro Hx.
  generalize (Cauchy_seq_impl_ex_lim_seq y (Cauchy_seq_pr2 u Cu)).
  set (ly := Cauchy_lim_seq y (Cauchy_seq_pr2 u Cu)) ; clearbody ly ; intro Hy.
  exists (NR_to_hr (lx,,ly)).
  intros c Hc.
  apply ispositive_Dcuts_half in Hc.
  generalize (Hx _ Hc) (Hy _ Hc) ;
    apply hinhfun2 ; clear Hy Hx ;
    intros (Nx,Hx) (Ny,Hy).
  exists (max Nx Ny) ; intros n Hn.
  rewrite <- Hxy ; simpl pr1.
  apply Dcuts_max_lt.
  - destruct hr_to_NR as (z,(Hz',Hz)) ; simpl pr1 ; clear Hz'.
    eapply istrans_le_lt_ltNonnegativeReals.
    assert (Hlim : pr1 (NR_to_hr (x n,, y n) - NR_to_hr (lx,, ly))%rng (x n + ly ,, y n + lx)).
    { apply hinhpr ; exists 0 ; reflexivity. }
    apply_pr2_in hr_repres Hlim.
    apply (Hz _ Hlim).
    simpl pr1.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (y n + lx)).
    rewrite iscomm_plusNonnegativeReals, Dcuts_minus_plus_max.
    apply Dcuts_max_lt.
    + rewrite (double_Dcuts_half c), (iscomm_plusNonnegativeReals (y n)), (isassoc_plusNonnegativeReals lx (y n)), <- (isassoc_plusNonnegativeReals (y n)), (iscomm_plusNonnegativeReals (y n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (lx + _)).
      apply plusNonnegativeReals_ltcompat.
      apply Hx.
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
      apply_pr2 Hy.
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_Dcuts_half.
  - destruct hr_to_NR as (z,(Hz',Hz)) ; simpl pr1 ; clear Hz'.
    eapply istrans_le_lt_ltNonnegativeReals.
    assert (Hlim : pr1 (NR_to_hr (x n,, y n) - NR_to_hr (lx,, ly))%rng (x n + ly ,, y n + lx)).
    { apply hinhpr ; exists 0 ; reflexivity. }
    apply_pr2_in hr_repres Hlim.
    apply_pr2 (Hz _ Hlim).
    simpl pr2.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (x n + ly)).
    rewrite iscomm_plusNonnegativeReals, Dcuts_minus_plus_max.
    apply Dcuts_max_lt.
    + rewrite (double_Dcuts_half c), (iscomm_plusNonnegativeReals (x n)), (isassoc_plusNonnegativeReals ly (x n)), <- (isassoc_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (x n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (ly + _)).
      apply plusNonnegativeReals_ltcompat.
      apply Hy.
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
      apply_pr2 Hx.
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_Dcuts_half.
Qed.
