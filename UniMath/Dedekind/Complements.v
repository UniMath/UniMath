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

Lemma nattorig_nat :
  ∀ n : nat, nattorig (X := natcommrig) n = n.
Proof.
  induction n.
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
    destruct Hy as [Hy | <-].
    + apply hinhpr.
      exists 1%nat.
      exact Hy.
    + apply hinhpr.
      exists 2%nat.
      rewrite nattorig_nat, !multsnm ; simpl.
      rewrite natplusr0.
      apply natgthandplusl, natgthsnn.
  - intros n.
    apply hinhpr.
    exists (S n).
    rewrite nattorig_nat.
    now apply natgthsnn.
  - intros n.
    apply hinhpr.
    now exists 1%nat.
Defined.

Definition isarchhz : isarchrng (X := hz) hzgth.
Proof.
  simple refine (isarchrigtorng _ _ _ _ _ _).
  - reflexivity.
  - intros n m k.
    apply istransnatgth.
  - admit. (*apply isarchnat.*)
Admitted.

Lemma isarchhq :
  isarchfld (X := hq) hqgth.
Proof.
  simple refine (isarchfldfrac hzintdom _ _ _ _ _ _ _ _).
  - exact isirreflhzgth.
  - exact istranshzgth.
  - apply isarchhz.
Qed.

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