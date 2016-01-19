(** * Additionals theorems and definitions *)

(** ** About nat *)

Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.

Lemma max_le_l : ∀ n m : nat, (n <= max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; reflexivity.
  - destruct m.
    + now apply isreflnatleh.
    + now apply IHn.
Qed.
Lemma max_le_r : ∀ n m : nat, (m <= max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; now apply isreflnatleh.
  - destruct m.
    + reflexivity.
    + now apply IHn.
Qed.

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.NumberSystems.RationalNumbers.

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
  intros Hx.
  apply hqlthandmultlinv with x.
  - exact Hx.
  - rewrite hqmultx0.
    rewrite hqisrinvmultinv.
    + exact hq1_gt0.
    + apply hqgth_hqneq.
      exact Hx.
Qed.

Lemma hztohqandleh':
  ∀ n m : hz, (hztohq n <= hztohq m)%hq -> hzleh n m.
Admitted.
Lemma hztohqandlth':
  ∀ n m : hz, (hztohq n < hztohq m)%hq -> hzlth n m.
Admitted.

Lemma Snattohz_neq0 :
  ∀ n, nattohz (S n) != 0%hz.
Proof.
  intro n.
  apply nattohzandneq.
  easy.
Qed.
Definition Snattohz (n : nat) : intdomnonzerosubmonoid hzintdom.
Proof.
  exists (nattohz (S n)).
  now apply Snattohz_neq0.
Defined.
Definition hznattohq (n : hz) (d : nat) : hq.
Proof.
  apply hzhztohq.
  - exact n.
  - exact (Snattohz d).
Defined.
Lemma hqtohznat : ∀ (x : hq),
  ∃ (n : hz) (d : nat), x = hznattohq n d.
Proof.
  intros X.
  generalize (pr1 (pr2 X)).
  apply hinhfun.
  intros x.
  destruct (hzneqchoice _ _ (pr2 (pr2 (pr1 x)))).
  - exists (pr1 (pr1 x)), (Nat.pred (hzabsval (pr1 (pr2 (pr1 x))))).
    eapply pathscomp0.
    eapply pathsinv0.
    exact (setquotl0 _ X x).
    apply iscompsetquotpr.
    apply hinhpr.
    simpl pr1 ; simpl pr2.
    exists one_intdomnonzerosubmonoid.
    apply (maponpaths (λ x, op x _)).
    apply maponpaths.
    eapply pathscomp0.
    2: apply (hzabsvalgth0 h).
    apply maponpaths.
    apply hzgthtoneq in h.
    apply hzabsvalneq0 in h.
    revert h.
    set (hzabsval (pr1 (pr2 (pr1 x)))).
    change (n ≠ 0 -> S (pred n) = n).
    destruct n ; intro.
    apply fromempty.
    now apply X0.
    reflexivity.
  - exists (- pr1 (pr1 x))%hz, (Nat.pred (hzabsval (pr1 (pr2 (pr1 x))))).
    eapply pathscomp0.
    eapply pathsinv0.
    exact (setquotl0 _ X x).
    apply iscompsetquotpr.
    apply hinhpr.
    simpl pr1 ; simpl pr2.
    exists one_intdomnonzerosubmonoid.
    apply (maponpaths (λ x, op x _)).
    change ((pr1 (pr1 x) * nattohz (S (Nat.pred (hzabsval (pr1 (pr2 (pr1 x)))))))%rng =
            ((- pr1 (pr1 x)) * pr1 (pr2 (pr1 x)))%rng).
    rewrite rnglmultminus, <- rngrmultminus.
    apply maponpaths.
    eapply pathscomp0.
    2: apply (hzabsvallth0 h).
    apply maponpaths.
    apply hzlthtoneq in h.
    apply hzabsvalneq0 in h.
    revert h.
    destruct (hzabsval (pr1 (pr2 (pr1 x)))) ; intro.
    apply fromempty.
    now apply h.
    reflexivity.
Qed.

Lemma intpartint0_hznat :
  ∀ (n : hz) (d : nat), intpartint0 (n ,, Snattohz d) = (hzabsval n / (S d))%nat.
Proof.
  intros n d.
  unfold intpartint0.
  apply maponpaths.
  unfold hzabsval, nattohz.
  apply (setquotunivcomm (eqrelabgrfrac nataddabmonoid) natset hzabsvalint
    hzabsvalintcomp).
Qed.
Lemma intpart0_hznat :
  ∀ (n : hz) (d : nat), intpart0 (hznattohq n d) = (hzabsval n / (S d))%nat.
Proof.
  intros n d.
  unfold intpart0.
  unfold hznattohq, hzhztohq.
  rewrite (setquotunivcomm (eqrelabmonoidfrac hzmultabmonoid (intdomnonzerosubmonoid hzintdom))
     natset intpartint0 iscompintpartint0).
  apply intpartint0_hznat.
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
    apply (pr2 (hzgth n m) _ _).
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
    apply (pr2 (hzlth n m) _ _).
Qed.

(*Lemma hznattohq_gth :
  ∀ n d n' d',
    hzgth (n * (nattohz (S d')))%hz (n' * (nattohz (S d)))%hz
    <-> hznattohq n d > hznattohq n' d'.
Proof.
  Opaque hzgth.
  intros.
  split.
  - intro Hgt.
    apply hinhpr.
    exists one_rngpossubmonoid.
    apply hzgthandmultr.
    + destruct one_rngpossubmonoid as [one Hone].
      simpl in Hone.
      exact Hone.
    + unfold weqfldfracgtint_f.
      simpl pr2 ; simpl pr1.
      assert (Hd : forall d, hzgth (nattohz (S d)) 0%hz).
      { intro.
        apply nattohzandgth.
        now apply (natgthsn0 _). }
      pattern (hzneqchoice (nattohz (S d)) 0%rng (Snattohz_neq0 d)).
      rewrite (hzneqchoice_l (nattohz (S d)) 0%hz (Snattohz_neq0 d) (Hd d)).
      pattern (hzneqchoice (nattohz (S d')) 0%rng (Snattohz_neq0 d')).
      rewrite (hzneqchoice_l (nattohz (S d')) 0%hz (Snattohz_neq0 d') (Hd d')).
      simpl pr2 ; simpl pr1.

Qed.*)

Lemma hztohq_opp :
  ∀ n : hz, hztohq (- n)%hz = - hztohq n.
Proof.
Admitted.

Lemma intpart0_carac :
  ∀ x : hq, hztohq (nattohz (intpart0 x)) <= x ∧ x < hztohq (nattohz (intpart0 x)) + 1.
Proof.
  intros x.
  generalize (hqtohznat x).
  apply hinhuniv.
  intros (n,(d)) ->.
  rewrite intpart0_hznat.
Admitted.

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
Admitted.
Definition intpart' (x : hq) : hz :=
  (- intpart (- x)%hq)%hz.
Lemma intpart'_carac :
  ∀ x : hq, hztohq (intpart' x) - 1 < x × x <= hztohq (intpart' x).
Admitted.

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