(** * Additionals theorems and definitions *)

(** ** About nat *)

Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.
Require Import UniMath.Ktheory.Utilities.

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
  intros x Hx.
  apply hqlthandmultlinv with x.
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
Lemma natplus0 :
  ∀ x y : nat, (x + y)%nat = 0%nat -> x = 0%nat × y = 0%nat.
Proof.
  destruct x.
  - intros y.
    rewrite natplusl0.
    intros ->.
    easy.
  - intros y Hy.
    simpl in Hy.
    apply fromempty.
    now apply negpathssx0 in Hy.
Qed.
Lemma hztonatnat (x : hz) :
  Σ n : nat × nat, pr1 x n × (pr1 n = 0%nat ∨ pr2 n = 0%nat).
Proof.
  destruct x as (X,(x,(Hx1,Hx2))) ; simpl pr1.
  revert x.
  apply hinhuniv'.
  { assert (Hnat : isaset (nat × nat))
      by (apply isasetdirprod ; exact isasetnat).
    apply isaproptotal2'.
    - exact Hnat.
    - intros x.
      apply isapropdirprod ;
      apply pr2.
    - intros (n,n') (m,m') ;
      simpl ;
      intros (Xn,Hn) (Xm,Hm).
      revert Hn Hm.
      apply hinhuniv2'.
      apply Hnat.
      intros Hx Hy.
      generalize (Hx2 _ _ Xn Xm).
      apply hinhuniv'.
      apply Hnat.
      simpl ; intros (c,Hc).
      apply natplusrcan in Hc.
      destruct Hx as [Hx | Hx] ;
        destruct Hy as [Hy | Hy] ;
        rewrite Hx, Hy in Hc |- *.
      + rewrite !natplusl0 in Hc.
        now rewrite Hc.
      + rewrite natplusr0 in Hc.
        apply pathsinv0, natplus0 in Hc.
        now rewrite (pr2 Hc), (pr1 Hc).
      + rewrite natplusr0 in Hc.
        apply natplus0 in Hc.
        now rewrite (pr2 Hc), (pr1 Hc).
      + rewrite !natplusr0 in Hc.
        now rewrite Hc. }
  intros (n,Hn).
  destruct (natgthorleh (pr1 n) (pr2 n)) as [Hgt | Hle].
  - exists ((pr1 n - pr2 n)%nat,,0%nat) ; split.
    revert Hn ; apply Hx1.
    apply hinhpr ; exists 0%nat ; simpl.
    rewrite !natplusr0.
    rewrite minusplusnmm.
    reflexivity.
    apply natlthtoleh, Hgt.
    now apply hinhpr ; right.
  - exists (0%nat,,(pr2 n - pr1 n)%nat) ; split.
    revert Hn ; apply Hx1.
    apply hinhpr ; exists 0%nat ; simpl.
    rewrite !natplusr0, natplusl0.
    rewrite natpluscomm, minusplusnmm.
    reflexivity.
    exact Hle.
    now apply hinhpr ; left.
Qed.

Lemma hqtohzhz (x : hq) : Σ y : hz × intdomnonzerosubmonoid hzintdom, pr1 x y × (hzlth 0%hz (pr1 (pr2 y)))%hz × ∀ z : hz × intdomnonzerosubmonoid hzintdom, (hzabsval (pr1 y) <= hzabsval (pr1 z))%nat.
Proof.

Qed.

Definition nattohq (n : nat) : hq :=
  hztohq (nattohz n).
Lemma hztohq_opp :
  ∀ x : hz, hztohq (- x)%hz = - hztohq x.
Admitted.
Lemma isdistr_opp_plus :
  ∀ x y : hq, - x + - y = - (x + y).
Admitted.
Lemma plus_opp_r :
  ∀ x : hq, x + - x = 0.
Admitted.
Lemma opp_zero :
  - 0 = 0.
Admitted.
Lemma lt_opp :
  ∀ x y : hq, x < y <-> - y < - x.
Admitted.
Lemma le_opp :
  ∀ x y : hq, x <= y <-> - y <= - x.
Admitted.
Lemma isinvolutive_opp :
  ∀ x : hq, - - x = x.
Admitted.
Lemma intpart0_opp :
  ∀ x : hq, intpart0 (- x) = intpart0 x.
Admitted.

Lemma isintpart_intpart0_le :
  ∀ x : hq, 0 <= x -> nattohq (intpart0 x) <= x.
Proof.
  intros X Hx0.
  Search hq hz.
  Print hqgth.
  unfold intpart0.
  unfold nattohq.
  unfold nattohz.
Qed.
Lemma isintpart_intpart0_lt :
  ∀ p : hq, 0 <= p -> p < nattohq (intpart0 p) + 1.
Qed.

Lemma isintpart_intpart_le :
  ∀ x : hq, hztohq (intpart x) <= x.
Proof.
  intros x.
  unfold intpart.
  destruct hqlthorgeh as [Hlt | Hle].
  + destruct isdeceqhq as [Heq | Hneq].
    * rewrite hztohq_opp.
      apply hqlehandpluslinv with (- x).
      rewrite isdistr_opp_plus.
      rewrite Heq.
      rewrite hqlminus.
      rewrite opp_zero.
      apply isreflhqleh.
    * rewrite hztohq_opp.
      apply (pr2 (le_opp _ _)).
      rewrite isinvolutive_opp.
      apply hqlthtoleh.
      rewrite hztohqandplus.
      rewrite hztohqand1.
      rewrite <- intpart0_opp.
      rewrite hqpluscomm.
      apply isintpart_intpart0_lt.
      apply (pr2 (le_opp _ _)).
      rewrite isinvolutive_opp.
      rewrite opp_zero.
      apply hqlthtoleh.
      exact Hlt.
  + apply isintpart_intpart0_le.
    exact Hle.
Qed.
Lemma isintpart_intpart_lt :
  ∀ x : hq, x < hztohq (intpart x) + 1.
Proof.
  intros x.
  unfold intpart.
  destruct hqlthorgeh as [Hlt | Hle].
  - destruct isdeceqhq as [Heq | Hneq].
    + rewrite hztohq_opp.
      apply hqlthandpluslinv with (hztohq (nattohz (intpart0 x))).
      rewrite hqpluscomm.
      rewrite Heq.
      rewrite <- hqplusassoc.
      rewrite (plus_opp_r (hztohq (nattohz (intpart0 x)))).
      rewrite hqplusl0.
      exact hq1_gt0.
    + rewrite hztohq_opp.
      rewrite hqpluscomm.
      rewrite hztohqandplus.
      rewrite hztohqand1.
      rewrite <- isdistr_opp_plus.
      rewrite <- hqplusassoc.
      rewrite (plus_opp_r 1).
      rewrite hqplusl0.
      apply (pr2 (lt_opp _ _)).
      rewrite isinvolutive_opp.
      rewrite <- intpart0_opp.
      destruct (fun H => hqlehchoice _ _ (isintpart_intpart0_le (- x) H)) as [Hlt' | Heq].
      apply (pr2 (le_opp _ _)).
      rewrite isinvolutive_opp.
      rewrite opp_zero.
      apply hqlthtoleh.
      exact Hlt.
      exact Hlt'.
      apply fromempty.
      apply Hneq.
      rewrite <- intpart0_opp.
      change (x + nattohq (intpart0 (- x)) = 0).
      rewrite Heq.
      apply plus_opp_r.
  - apply isintpart_intpart0_lt.
    exact Hle.
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