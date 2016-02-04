(** * Additionals theorems and definitions *)

(** ** About nat *)

Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.
Require Import UniMath.Ktheory.Utilities.

Lemma max_le_l : ∀ n m : nat, (n ≤ max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; reflexivity.
  - destruct m.
    + now apply isreflnatleh.
    + now apply IHn.
Qed.
Lemma max_le_r : ∀ n m : nat, (m ≤ max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; now apply isreflnatleh.
  - destruct m.
    + reflexivity.
    + now apply IHn.
Qed.

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
  apply (hzgthtoneq 1%hz 0%hz).
  rewrite <- nattohzand1.
  apply nattohzandgth.
  apply paths_refl.
Qed.
Definition one_intdomnonzerosubmonoid : intdomnonzerosubmonoid hzintdom.
Proof.
  exists 1%hz ; simpl.
  exact hzone_neg_hzzero.
Defined.

Opaque hz.

Lemma hq2eq1plus1 :
  2 = 1 + 1.
Proof.
  rewrite <- hztohqand1, <- nattohzand1.
  now rewrite <- hztohqandplus, <- nattohzandplus.
Qed.

Lemma hq2_gt0 : 2 > 0.
Proof.
  rewrite <- hztohqand0, <- nattohzand0.
  now apply hztohqandgth, nattohzandgth.
Qed.
Lemma hq1_gt0 : 1 > 0.
Proof.
  rewrite <- hztohqand0, <- hztohqand1.
  rewrite <- nattohzand1, <- nattohzand0.
  now apply hztohqandgth, nattohzandgth.
Qed.
Lemma hq1ge0 : (0 <= 1)%hq.
Proof.
  now apply hqlthtoleh, hq1_gt0.
Qed.

Lemma hqgth_hqneq :
  forall x y : hq, x > y -> hqneq x y.
Proof.
  intros x y Hlt Heq.
  rewrite Heq in Hlt.
  now apply isirreflhqgth with y.
Qed.

Lemma hqldistr :
  forall x y z, x * (y + z) = x * y + x * z.
Proof.
  intros x y z.
  now apply rngldistr.
Qed.

Lemma hqmult2r :
  forall x : hq, x * 2 = x + x.
Proof.
  intros x.
  now rewrite hq2eq1plus1, hqldistr, (hqmultr1 x).
Qed.

Lemma hqplusdiv2 : forall x : hq, x = (x + x) / 2.
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
  forall x y : hq, x < y -> total2 (fun z => dirprod (x < z) (z < y)).
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
  forall n m : hq,
    0 <= n -> 0 <= m -> 0 <= (n + m).
Proof.
  intros n m Hn Hm.
  eapply istranshqleh, hqlehandplusl, Hm.
  now rewrite hqplusr0.
Qed.

Lemma hq0lehandmult:
  ∀ n m : hq, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
  intros n m.
  exact hqmultgeh0geh0.
Qed.

Lemma hq0leminus :
  forall r q : hq, r <= q -> 0 <= q - r.
Proof.
  intros r q Hr.
  apply hqlehandplusrinv with r.
  unfold hqminus.
  rewrite hqplusassoc, hqlminus.
  now rewrite hqplusl0, hqplusr0.
Qed.

Lemma hqinv_gt0 (x : hq) : 0 < x -> 0 < / x.
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

Lemma isaproptotal2' {X : UU} (P : X -> UU) :
  isaset X ->
  isPredicate P ->
  (∀ x y : X, P x -> P y -> x = y) ->
  isaprop (Σ x : X, P x).
Proof.
  intros X P HX HP Heq x y ; simpl.
  eapply iscontrweqb.
  apply subtypeInjectivity.
  exact HP.
  rewrite (Heq (pr1 y) (pr1 x)).
  apply iscontrloopsifisaset.
  exact HX.
  exact (pr2 y).
  exact (pr2 x).
Qed.
Lemma hinhuniv' {P X : UU} :
  isaprop P -> (X -> P) -> (∥ X ∥ -> P).
Proof.
  intros P X HP Hx.
  apply (hinhuniv (P := hProppair _ HP)).
  exact Hx.
Qed.
Lemma hinhuniv2' {P X Y : UU} :
  isaprop P -> (X -> Y -> P) -> (∥ X ∥ -> ∥ Y ∥ -> P).
Proof.
  intros P X Y HP Hxy.
  apply (hinhuniv2 (P := hProppair _ HP)).
  exact Hxy.
Qed.

Lemma hztohqandleh':
  ∀ n m : hz, (hztohq n <= hztohq m)%hq -> hzleh n m.
Proof.
  intros n m Hle Hlt.
  apply Hle.
  apply hztohqandgth.
  exact Hlt.
Qed.
Lemma hztohqandlth':
  ∀ n m : hz, (hztohq n < hztohq m)%hq -> hzlth n m.
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
  ∀ n : nat, nattorig (X := hz) n = nattohz n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - rewrite nattorigS, IHn.
    apply pathsinv0, nattohzandS.
Qed.

Lemma isarchnat :
  isarchrig natcommrig natgth.
Proof.
  intros x y Hy0.
  apply hinhpr.
  exists (S (x / y)).
  rewrite <- nattorig_natmult.
  assert (∀ n, nattorig (X := natcommrig) n = n).
  { induction n.
    reflexivity.
    rewrite nattorigS, IHn.
    reflexivity. }
  rewrite X.
  change (((S (x / y)) * y) > x)%nat.
  simpl mul.
  pattern x at 2.
  rewrite (natdivremrule x y), natpluscomm.
  apply natgthandplusr, lthnatrem.
  apply natgthtoneq, Hy0.
  apply natgthtoneq, Hy0.
Defined.

Definition isarchhz : isarchrng hz hzgth.
Proof.
  simple refine (isarchrigtorng_gt _ _ _ _ _ _ _ _).
  - intros n.
    apply hinhpr.
    exists 1%nat.
    now rewrite natpluscomm.
  - apply ex_partal_minus_imply_week.
    + reflexivity.
    + intros n m k.
      apply istransnatgth.
    + split ; intros x y z.
      apply natgthandplusl.
      apply natgthandplusr.
    + apply isarchnat.
    + intros x y H.
      apply hinhpr.
      exists (x - y)%nat.
      split.
      now apply minusgth0.
      rewrite natpluscomm, minusplusnmm.
      reflexivity.
      now apply natgthtogeh.
  - now apply paths_refl.
  - intros n m k.
    apply istransnatgth.
  - apply isarchnat.
Defined.

Lemma isarchhq :
  isarchfld' hq hqgth.
Proof.
  simple refine (isarchfldfrac' hzintdom _ _ _ _ _ _ _).
  - intros n m.
    apply hzgthtogeh.
  - apply isarchhz.
Qed.

(*

(** ** intpart is correct *)

Lemma weqfldfracgt_f_b :
  ∀ (X : intdom) (is : isdeceq X) (R : hrel X)
    is0 is1 is2 is3 (Rdec : neqchoice R),
  ∀ (x : commrngfrac X (rngpossubmonoid X is1 is2))
    (x' : fldfrac X is),
    x' = (weqfldfracgt_b X is is1 is2 is3 x) ->
   weqfldfracgt_f X is is0 is1 is2 Rdec x' = x.
Proof.
  intros.
  generalize (pr1 (pr2 x)).
  apply hinhuniv'.
  apply isasetsetquot.
  intros y ; revert X0.
  rewrite <- (setquotl0 _ x y).
  unfold weqfldfracgt_b ; rewrite setquotfuncomm.
  intros ->.
  unfold weqfldfracgt_f ; rewrite setquotfuncomm.
  apply iscompsetquotpr.
  apply hinhpr.
  exists (1%rng ,, is2).
  unfold weqfldfracgtint_f ; simpl.
  destruct Rdec ; simpl.
  - reflexivity.
  - change ((- pr1 (pr1 y) * pr1 (pr2 (pr1 y)) * 1)%rng = (pr1 (pr1 y) * - pr1 (pr2 (pr1 y)) * 1)%rng).
    rewrite rngrmultminus, !rnglmultminus.
    reflexivity.
Qed.
Lemma weqfldfracgt_b_f :
  ∀ (X : intdom) (is : isdeceq X) (R : hrel X)
    is0 is1 is2 is3 (Rdec : neqchoice R),
  ∀ (x : fldfrac X is) (x' : commrngfrac X (rngpossubmonoid X is1 is2)),
    x' = (weqfldfracgt_f X is is0 is1 is2 Rdec x) ->
    weqfldfracgt_b X is is1 is2 is3 x' = x.
Proof.
  intros.
  generalize (pr1 (pr2 x)).
  apply hinhuniv'.
  apply isasetsetquot.
  intros y ; revert X0.
  rewrite <- (setquotl0 _ x y).
  unfold weqfldfracgt_f ; rewrite setquotfuncomm.
  intros ->.
  unfold weqfldfracgt_b ; rewrite setquotfuncomm.
  apply iscompsetquotpr.
  apply hinhpr.
  assert (is4 : (1%rng : X) != 0%rng).
  { intros H.
    rewrite H in is2.
    exact (is3 _ is2). }
  exists (1%rng ,, is4).
  unfold weqfldfracgtint_f ; simpl.
  destruct Rdec ; simpl.
  - reflexivity.
  - change ((- pr1 (pr1 y) * pr1 (pr2 (pr1 y)) * 1)%rng = (pr1 (pr1 y) * - pr1 (pr2 (pr1 y)) * 1)%rng).
    rewrite rngrmultminus, !rnglmultminus.
    reflexivity.
Qed.

Lemma intpart0_hznat :
  ∀ (x : hq) (x' : commrngfrac hzintdom
           (rngpossubmonoid hzintdom isrngmulthzgth
              (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)))),
    x' = weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x ->
    ∀ n, pr1 x' n ->
      intpart0 x = (hzabsval (pr1 n) / (hzabsval (pr1 (pr2 n))))%nat.
Proof.
  intros x x' Hx' n Hn.
  rewrite <- (weqfldfracgt_b_f hzintdom isdeceqhz _ isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) isirreflhzgth hzneqchoice x x' Hx').
  clear -Hn.
  unfold weqfldfracgt_b.
  rewrite <- (setquotl0 _ x' (n,,Hn)).
  rewrite setquotfuncomm.
  unfold intpart0.
  rewrite (setquotunivcomm (eqrelabmonoidfrac hzmultabmonoid (intdomnonzerosubmonoid hzintdom))
     natset intpartint0 iscompintpartint0).
  reflexivity.
Qed.

Definition one_rngpossubmonoid : rngpossubmonoid hzintdom isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)).
Proof.
  apply intdomnonzerotopos.
  exact isplushrelhzgth.
  exact hzneqchoice.
  exact one_intdomnonzerosubmonoid.
Defined.
Lemma hzneqchoice_l :
  ∀ (n m : hz) (Hneq : n != m) (Hgt : hzgth n m), hzneqchoice n m Hneq = ii1 Hgt.
Proof.
  intros n m Hneq Hgt.
  destruct hzneqchoice.
  - apply maponpaths.
    apply proofirrelevance.
    apply pr2.
  - apply fromempty.
    revert Hgt.
    apply hzlehtoneghzgth.
    apply hzlthtoleh.
    exact h.
Qed.
Lemma hzneqchoice_r :
  ∀ (n m : hz) (Hneq : n != m) (Hlt : hzlth n m), hzneqchoice n m Hneq = ii2 Hlt.
Proof.
  intros n m Hneq Hlt.
  destruct hzneqchoice.
  - apply fromempty.
    revert h.
    apply hzlehtoneghzgth.
    apply hzlthtoleh.
    exact Hlt.
  - apply maponpaths.
    apply proofirrelevance.
    apply pr2.
Qed.

Lemma hznattohq_gth :
  ∀ x y : hq,
    let x' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x in
    let y' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice y in
    ∀ n m,
      pr1 x' n -> pr1 y' m ->
      ((hzgth (pr1 n * (pr1 (pr2 m)))%hz (pr1 m * (pr1 (pr2 n)))%hz
    <-> x > y)).
Proof.
  intros x y x' y' n m Hn Hm.
  unfold hqgth.
  unfold fldfracgt.
  change (weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x) with x'.
  change (weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice y) with y'.
  rewrite <- (setquotl0 _ x' (n,,Hn)), <- (setquotl0 _ y' (m,,Hm)).
  simpl pr1 ; clear.
  unfold commrngfracgt, abmonoidfracrel, quotrel.
  rewrite setquotuniv2comm.
  split.
  - intros Hgt.
    apply hinhpr.
    exists one_rngpossubmonoid.
    apply hzgthandmultr.
    + destruct one_rngpossubmonoid as [one Hone].
      simpl in Hone.
      exact Hone.
    + exact Hgt.
  - apply hinhuniv.
    intros (c,Hc).
    apply hzgthandmultrinv with (pr1 c).
    + generalize (pr2 c).
      now simpl.
    + exact Hc.
Qed.

Lemma hznattohq_lth :
  ∀ x y : hq,
    let x' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x in
    let y' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice y in
    ∀ n m,
      pr1 x' n -> pr1 y' m ->
      ((hzlth (pr1 n * (pr1 (pr2 m)))%hz (pr1 m * (pr1 (pr2 n)))%hz
    <-> x < y)).
Proof.
  intros.
  now apply hznattohq_gth.
Qed.
Lemma hznattohq_geh :
  ∀ x y : hq,
    let x' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x in
    let y' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice y in
    ∀ n m,
      pr1 x' n -> pr1 y' m ->
      ((hzgeh (pr1 n * (pr1 (pr2 m)))%hz (pr1 m * (pr1 (pr2 n)))%hz
    <-> x >= y)).
Proof.
  intros.
  split.
  - intros Hge Hgt.
    apply Hge.
    eapply (pr2 (hznattohq_gth _ _ _ _ X0 X)).
    exact Hgt.
  - intros Hge Hgt.
    apply Hge.
    eapply (pr1 (hznattohq_gth _ _ _ _ X0 X)).
    exact Hgt.
Qed.
Lemma hznattohq_leh :
  ∀ x y : hq,
    let x' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x in
    let y' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice y in
    ∀ n m,
      pr1 x' n -> pr1 y' m ->
      ((hzleh (pr1 n * (pr1 (pr2 m)))%hz (pr1 m * (pr1 (pr2 n)))%hz
    <-> x <= y)).
Proof.
  intros.
  now apply hznattohq_geh.
Qed.

Lemma hztohq_hznattohq :
  ∀ n H1,
    pr1 (weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice (hztohq n)) (n ,, (1%rng,, H1)).
Proof.
  intros n H1.
  unfold weqfldfracgt_f, hztohq.
  unfold tofldfrac.
  rewrite setquotfuncomm.
  unfold weqfldfracgtint_f.
  simpl hzneqchoice.
  pattern (hzneqchoice 1%rng 0%rng (nonzeroax hzintdom)).
  rewrite (hzneqchoice_l _ _ (nonzeroax hzintdom) (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz))).
  simpl pr1 ; simpl pr2.
  apply hinhpr.
  exists one_rngpossubmonoid.
  reflexivity.
Qed.

(* Lemma hznattohq_eq :
  ∀ n d c,
    hznattohq (n * nattohz (S c))%hz (S d * c + d)
    = hznattohq n d.
Proof.
  intros.
  unfold hznattohq, hzhztohq.
  apply iscompsetquotpr.
  apply hinhpr.
  exists one_intdomnonzerosubmonoid.
  simpl.
  change (((n * nattohz (S c)) * nattohz (S d) * 1)%rng = (n * nattohz (S (d * c + c + d)) * 1)%rng).
  rewrite !rngassoc2, !rngrunax2.
  apply maponpaths.
  eapply pathscomp0.
  eapply pathsinv0.
  apply (nattohzandmult (S c) (S d)).
  apply maponpaths.
  simpl.
  rewrite natmultcomm, <- plus_n_Sm.
  simpl.
  reflexivity.
Qed.

Lemma hznattohq_plus :
  ∀ n d n' d',
    hznattohq n d + hznattohq n' d'
    = hznattohq (n * nattohz (S d') + n' * nattohz (S d))%hz (S d * d' + d).
Proof.
  intros.
  unfold hznattohq, hzhztohq.
  apply iscompsetquotpr.
  apply hinhpr.
  exists one_intdomnonzerosubmonoid.
  simpl.
  apply map_on_two_paths.
  2: reflexivity.
  apply map_on_two_paths.
  apply map_on_two_paths.
  apply rngcomm2.
  apply rngcomm2.
  eapply pathscomp0, nattohzandmult.
  apply maponpaths.
  simpl.
  rewrite (natmultcomm _ (S _)), <- plus_n_Sm, natmultcomm, natplusassoc, (natpluscomm d').
  simpl.
  rewrite natplusassoc.
  reflexivity.
Qed.
Lemma hznattohq_plus' :
  ∀ n n' d,
    hznattohq n d + hznattohq n' d
    = hznattohq (n + n')%hz d.
Proof.
  intros.
  rewrite hznattohq_plus.
  assert ((n * nattohz (S d) + n' * nattohz (S d))%hz = ((n + n') * nattohz (S d))%hz).
  { apply pathsinv0.
    apply rngrdistr. }
  rewrite X ; clear X.
  apply hznattohq_eq.
Qed.
Lemma hznattohq_opp :
  ∀ n d,
    - hznattohq n d
    = hznattohq (- n)%hz d.
Proof.
  intros.
  unfold hznattohq, hzhztohq.
  apply iscompsetquotpr.
  apply hinhpr.
  exists one_intdomnonzerosubmonoid.
  simpl.
  apply map_on_two_paths.
  2: reflexivity.
  apply map_on_two_paths.
  2: reflexivity.
  apply (rngmultwithminus1 _ n).
Qed.*)

Lemma hztohq_opp :
  ∀ n : hz, hztohq (- n)%hz = - hztohq n.
Proof.
  intros n.
  unfold hztohq.
  apply iscompsetquotpr.
  apply hinhpr.
  exists one_intdomnonzerosubmonoid ; simpl.
  apply (maponpaths (λ x, (x * _)%rng)).
  apply (maponpaths (λ x, (x * _)%rng)).
  apply pathsinv0.
  apply rngmultwithminus1.
Qed.

Lemma intpart0_carac :
  ∀ x : hq, 0 <= x -> hztohq (nattohz (intpart0 x)) <= x ∧ x < hztohq (nattohz (S (intpart0 x))).
Proof.
  intros x Hx.
  set (x' := weqfldfracgt_f hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz)) hzneqchoice x).
  set (n := pr1 (pr2 x')).
  generalize n ; clear n.
  apply hinhuniv ; intros n.
  rewrite (intpart0_hznat x x' (paths_refl _) (pr1 n) (pr2 n)).
  set ((pr2 (hznattohq_leh 0 x _ _ (hztohq_hznattohq 0%hz (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz))) (pr2 n))) Hx).
  clearbody h ; clear Hx ; rename h into Hx.
  simpl pr1 in Hx.
  rewrite hzmult0x, hzmultr1 in Hx.
  split.
  - eapply (hznattohq_leh _ _).
    + apply (hztohq_hznattohq _ (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz))).
    + exact (pr2 n).
    + simpl pr1 ; simpl pr2.
      change (hzleh
     (nattohz (hzabsval (pr1 (pr1 n)) / hzabsval (pr1 (pr2 (pr1 n)))) *
      pr1 (pr2 (pr1 n)))%hz (pr1 (pr1 n) * 1)%hz).
      rewrite hzmultr1.
      revert Hx.
      set (pr1 n).
      change (pr1 n) with y.
      clearbody y ; clear ; intros Hy.
      destruct y as (n,(m,Hm)).
      simpl pr1 in Hy |- *.
      simpl in Hm.
      pattern n at 2 ;
        rewrite <- (hzabsvalgeh0 Hy).
      pattern m at 2 ;
        rewrite <- (hzabsvalgeh0 (hzlthtoleh _ _ Hm)).
      rewrite <- nattohzandmult.
      apply nattohzandleh.
      apply natlehmultnatdiv.
      apply hzabsvalneq0.
      apply hzgthtoneq.
      exact Hm.
  - eapply hznattohq_lth.
    + exact (pr2 n).
    + apply (hztohq_hznattohq _ (ct (hzgth, isdecrelhzgth, 1%hz, 0%hz))).
    + simpl pr1 ; simpl pr2.
      change (hzlth (pr1 (pr1 n) * 1)%hz
     (nattohz (S (hzabsval (pr1 (pr1 n)) / hzabsval (pr1 (pr2 (pr1 n))))) *
      pr1 (pr2 (pr1 n)))%hz).
      rewrite hzmultr1.
      revert Hx.
      set (pr1 n).
      change (pr1 n) with y.
      clearbody y ; clear ; intros Hy.
      destruct y as (n,(m,Hm)).
      simpl pr1 in Hy |- *.
      simpl in Hm.
      pattern n at 1 ;
        rewrite <- (hzabsvalgeh0 Hy).
      pattern m at 2 ;
        rewrite <- (hzabsvalgeh0 (hzlthtoleh _ _ Hm)).
      rewrite <- nattohzandmult.
      apply nattohzandlth.
      simpl mul.
      pattern (hzabsval n) at 1.
      rewrite (natdivremrule (hzabsval n) (hzabsval m)).
      rewrite natpluscomm.
      apply natlthandplusl.
      apply lthnatrem.
      apply hzabsvalneq0, hzgthtoneq, Hm.
      apply hzabsvalneq0, hzgthtoneq, Hm.
Qed.

Lemma hqopp_opp :
  ∀ x : hq, - - x = x.
Proof.
  intros.
  apply hqplusrcan with (- x).
  rewrite hqlminus.
  apply pathsinv0, hqrminus.
Qed.
Lemma hqopp_distr :
  ∀ x y : hq, - (x + y) = - x + - y.
Proof.
  intros.
  apply hqplusrcan with (x + y).
  rewrite hqlminus.
  rewrite (hqpluscomm (- x)).
  rewrite <- hqplusassoc.
  rewrite (hqplusassoc (- y) (- x) x).
  rewrite hqlminus.
  rewrite hqplusr0.
  apply pathsinv0, hqlminus.
Qed.

Lemma hqopp_gth :
  ∀ x y : hq, x > y <-> - y > - x.
Proof.
  intros x y.
  split.
  - intro Hlt.
    apply hqgthandplusrinv with x.
    rewrite hqlminus.
    rewrite <- (hqlminus y).
    apply hqgthandplusl.
    exact Hlt.
  - intro Hlt.
    apply hqgthandpluslinv with (- x).
    rewrite hqlminus.
    rewrite <- (hqlminus y).
    apply hqgthandplusr.
    exact Hlt.
Qed.
Lemma hqopp_lth :
  ∀ x y : hq, x < y <-> - y < - x.
Proof.
  intros.
  apply hqopp_gth.
Qed.
Lemma hqopp_geh :
  ∀ x y : hq, x >= y <-> - y >= - x.
Proof.
  split ; intros Hge Hgt ; apply Hge.
  - apply (pr2 (hqopp_gth _ _)).
    exact Hgt.
  - apply (pr1 (hqopp_gth _ _)).
    exact Hgt.
Qed.
Lemma hqopp_leh :
  ∀ x y : hq, x <= y <-> - y <= - x.
Proof.
  intros.
  apply hqopp_geh.
Qed.
Lemma hzabsval_opp :
  ∀ x : hz, hzabsval (- x)%hz = hzabsval x.
Proof.
  intros X.
  generalize (pr1 (pr2 X)).
  apply hinhuniv'.
  now apply isasetnat.
  intro x.
  rewrite <- (setquotl0 _ X x).
  eapply pathscomp0.
  apply (setquotunivcomm (eqrelabgrfrac nataddabmonoid) natset).
  eapply pathscomp0, pathsinv0.
  2: apply (setquotunivcomm (eqrelabgrfrac nataddabmonoid) natset).
  simpl.
  unfold hzabsvalint ; simpl.
  destruct natgthorleh as [Hgt | Hle] ;
  destruct natgthorleh as [Hlt | Hge].
  - apply fromempty.
    generalize Hlt.
    apply natlehneggth.
    apply natlthtoleh.
    exact Hgt.
  - reflexivity.
  - reflexivity.
  - rewrite (isantisymmnatgeh _ _ Hle Hge).
    reflexivity.
Qed.
Lemma intpart0_opp :
  ∀ x : hq, intpart0 (- x) = intpart0 x.
Proof.
  intros X.
  unfold intpart0.
  generalize (pr1 (pr2 X)).
  apply hinhuniv'.
  now apply isasetnat.
  intros x.
  rewrite <- (setquotl0 _ X x).
  unfold hqsign, grinv ; simpl pr1.
  unfold commrngfracinv1.
  rewrite setquotfuncomm.
  rewrite !setquotunivcomm.
  unfold intpartint0.
  apply (maponpaths (λ x, (x / _)%nat)).
  simpl.
  change (hzabsval (-1 * pr1 (pr1 x))%rng = hzabsval (pr1 (pr1 x))).
  rewrite rngmultwithminus1.
  apply hzabsval_opp.
Qed.

Lemma intpart_carac :
  ∀ x : hq, hztohq (intpart x) <= x ∧ x < hztohq (intpart x) + 1.
Proof.
  intros x.
  simpl intpart ; unfold intpart.
  destruct hqlthorgeh as [Hx0 | Hx0].
  - destruct isdeceqhq as [Hxn | Hxn].
    + rewrite <- (hqlminus (hztohq (nattohz (intpart0 x)))) in Hxn.
      apply hqplusrcan in Hxn.
      pattern x at 2 3 ; rewrite Hxn.
      rewrite hztohq_opp.
      split.
      * apply isreflhqleh.
      * apply hqlthnsn.
    + rewrite hztohq_opp.
      rewrite hztohqandplus.
      rewrite hztohqand1.
      rewrite <- intpart0_opp.
      assert (Hx : 0 <= - x).
      { apply hqlthtoleh.
        apply hqlth0andminus.
        exact Hx0. }
      generalize (intpart0_carac (- x) Hx) ; intro H.
      split.
      * apply (pr2 (hqopp_leh _ _)).
        rewrite hqopp_opp.
        rewrite hqpluscomm.
        apply hqlthtoleh.
        rewrite hqpluscomm.
        rewrite <-hztohqand1, <- hztohqandplus.
        rewrite <- nattohzandS.
        exact (pr2 H).
      * pattern 1 at 2 ; rewrite <- (hqopp_opp 1).
        rewrite <- hqopp_distr.
        rewrite (hqpluscomm (_+_)).
        rewrite <- hqplusassoc.
        rewrite hqlminus.
        rewrite hqplusl0.
        apply (pr2 (hqopp_lth _ _)).
        rewrite hqopp_opp.
        destruct (hqlehchoice _ _ (pr1 H)) as [H0 | H0].
        exact H0.
        apply fromempty, Hxn.
        rewrite <- intpart0_opp, H0.
        apply hqrminus.
  - rewrite hqpluscomm.
    rewrite <-hztohqand1, <- hztohqandplus.
    rewrite <- nattohzandS.
    apply intpart0_carac.
    exact Hx0.
Qed.
Definition intpart' (x : hq) : hz :=
  (- intpart (- x)%hq)%hz.
Lemma intpart'_carac :
  ∀ x : hq, hztohq (intpart' x) - 1 < x × x <= hztohq (intpart' x).
Proof.
  intros x.
  unfold intpart'.
  generalize (intpart_carac (- x)) ; intros (H,H0).
  split.
  - apply (pr2 (hqopp_lth _ _)).
    unfold hqminus.
    rewrite hztohq_opp.
    rewrite <- hqopp_distr.
    rewrite hqopp_opp.
    exact H0.
  - apply (pr2 (hqopp_leh _ _)).
    rewrite hztohq_opp.
    rewrite hqopp_opp.
    exact H.
Qed.

Lemma intpart_id :
  ∀ n : hz, intpart (hztohq n) = n.
Proof.
  intros n.
  apply isantisymmhzleh.
  - apply hztohqandleh'.
    apply intpart_carac.
  - apply hzlthsntoleh.
    apply hztohqandlth'.
    rewrite hztohqandplus, hztohqand1.
    apply (pr2 (intpart_carac _)).
Qed.
Lemma intpart_le :
  ∀ n m : hq, (n <= m)%hq -> (hzleh (intpart n) (intpart m)).
Proof.
  intros n m Hle.
  apply hzlthsntoleh.
  apply hztohqandlth'.
  rewrite hztohqandplus, hztohqand1.
  eapply hqlehlthtrans, (pr2 (intpart_carac _)).
  eapply istranshqleh, Hle.
  now apply intpart_carac.
Qed.
 *)

Close Scope hq_scope.

(** ** A new tactic *)

Ltac apply_pr2 T :=
  first [ refine (pr2 (T) _)
        | refine (pr2 (T _) _)
        | refine (pr2 (T _ _) _)
        | refine (pr2 (T _ _ _) _)
        | refine (pr2 (T _ _ _ _) _)
        | refine (pr2 (T _ _ _ _ _) _)
        | refine (pr2 (T))
        | refine (pr2 (T _))
        | refine (pr2 (T _ _))
        | refine (pr2 (T _ _ _))
        | refine (pr2 (T _ _ _ _))
        | refine (pr2 (T _ _ _ _ _)) ].

Ltac apply_pr2_in T H :=
  first [ apply (pr2 (T)) in H
        | apply (fun H0 => pr2 (T H0)) in H
        | apply (fun H0 H1 => pr2 (T H0 H1)) in H
        | apply (fun H0 H1 H2 => pr2 (T H0 H1 H2)) in H
        | apply (fun H0 H1 H2 H3 => pr2 (T H0 H1 H2 H3)) in H
        | apply (fun H0 H1 H2 H3 H4 => pr2 (T H0 H1 H2 H3 H4)) in H ].