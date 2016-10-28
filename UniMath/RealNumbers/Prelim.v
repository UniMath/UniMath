(** * Additionals theorems and definitions *)

Require Export UniMath.Topology.Prelim.

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** ** for RationalNumbers.v *)

Require Export UniMath.Foundations.NumberSystems.RationalNumbers.
Require Export UniMath.Foundations.Algebra.Archimedean.
Require Export UniMath.Foundations.Algebra.Lattice.

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

Lemma hqgth_opp :
  Π x y : hq, x > y → - y > - x.
Proof.
  intros x y Hxy.
  apply hqgthandpluslinv with y.
  change (y - y > y + - x).
  rewrite hqrminus.
  apply hqgthandplusrinv with x.
  rewrite hqplusassoc, hqlminus, hqplusl0, hqplusr0.
  exact Hxy.
Qed.
Lemma hqgth_opp' :
  Π x y : hq, - x > - y → y > x.
Proof.
  intros x y Hxy.
  apply hqgth_opp in Hxy.
  rewrite !(grinvinv hq) in Hxy.
  exact Hxy.
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

(** ** nat is a lattice *)

Lemma min_id :
  Π n : nat, min n n = n.
Proof.
  intros n.
  induction n as [ | n IHn].
  - reflexivity.
  - change (S (min n n) = S n).
    apply maponpaths, IHn.
Qed.
Lemma max_id :
  Π n : nat, max n n = n.
Proof.
  intros n.
  induction n as [ | n IHn].
  - reflexivity.
  - change (S (max n n) = S n).
    apply maponpaths, IHn.
Qed.

Lemma isassoc_min :
  isassoc (X := hSetpair nat isasetnat) min.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m k.
    reflexivity.
  - intros m.
    induction m as [ | m _].
    + intros k.
      reflexivity.
    + intros k.
      induction k as [ | k _].
      * reflexivity.
      * change (S (min (min n m) k) = S (min n (min m k))).
        apply maponpaths, IHn.
Qed.
Lemma iscomm_min :
  iscomm (X := hSetpair nat isasetnat) min.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m.
    induction m as [ | m _].
    + reflexivity.
    + reflexivity.
  - intros m.
    induction m as [ | m _].
    + reflexivity.
    + change (S (min n m) = S (min m n)).
      apply maponpaths, IHn.
Qed.

Lemma isassoc_max :
  isassoc (X := hSetpair nat isasetnat) max.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m k.
    reflexivity.
  - intros m.
    induction m as [ | m _].
    + intros k.
      reflexivity.
    + intros k.
      induction k as [ | k _].
      * reflexivity.
      * change (S (max (max n m) k) = S (max n (max m k))).
        apply maponpaths, IHn.
Qed.
Lemma iscomm_max :
  iscomm (X := hSetpair nat isasetnat) max.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m.
    induction m as [ | m _].
    + reflexivity.
    + reflexivity.
  - intros m.
    induction m as [ | m _].
    + reflexivity.
    + change (S (max n m) = S (max m n)).
      apply maponpaths, IHn.
Qed.
Lemma isabsorb_min_max :
  Π n m : nat, min n (max n m) = n.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m.
    reflexivity.
  - intros m.
    induction m as [ | m _].
    + change (S (min n n) = S n).
      apply maponpaths, min_id.
    + change (S (min n (max n m)) = S n).
      apply maponpaths, IHn.
Qed.
Lemma isabsorb_max_min :
  Π n m : nat, max n (min n m) = n.
Proof.
  intros n.
  induction n as [ | n IHn].
  - intros m.
    reflexivity.
  - intros m.
    induction m as [ | m _].
    + reflexivity.
    + change (S (max n (min n m)) = S n).
      apply maponpaths, IHn.
Qed.

Lemma islatticeop_nat : islatticeop (X := hSetpair nat isasetnat) min max.
Proof.
  repeat split.
  - exact isassoc_min.
  - exact iscomm_min.
  - exact isassoc_max.
  - exact iscomm_max.
  - exact isabsorb_min_max.
  - exact isabsorb_max_min.
Qed.

Definition islattice_nat : islattice (hSetpair nat isasetnat) :=
  min ,, max ,, islatticeop_nat.

Lemma Llenat_correct :
  Π n m, n ≤ m <-> Lle islattice_nat n m.
Proof.
  intros n m.
  split.
  - revert m.
    induction n as [ | n IHn].
    + intros m H.
      reflexivity.
    + intros m.
      induction m as [ | m _].
      * change (false = true → O = S n).
        intros H.
        apply fromempty, nopathsfalsetotrue, H.
      * change (n ≤ m → S (min n m) = S n).
        intros H.
        apply maponpaths, IHn, H.
  - revert m.
    induction n as [ | n IHn].
    + intros m H.
      reflexivity.
    + intros m.
      induction m as [ | m _].
      * change (O = S n → false = true).
        intros H.
        apply fromempty, (negpaths0sx n), H.
      * change (S (min n m) = S n → n ≤ m).
        intros H.
        apply IHn.
        apply invmaponpathsS, H.
Qed.

(** ** hz is a lattice *)

Definition hzmin : binop hz.
Proof.
  intros x y.
  generalize (hzgthorleh x y) ;
    apply sumofmaps ;
    intros H.
  apply y.
  apply x.
Defined.
Definition hzmax : binop hz.
Proof.
  intros x y.
  generalize (hzgthorleh x y) ;
    apply sumofmaps ;
    intros H.
  apply x.
  apply y.
Defined.

(** ** hq is a lattice *)

Definition hqmin : binop hq.
Proof.
  intros x y.
  generalize (hqgthorleh x y) ;
    apply sumofmaps ;
    intros H.
  apply y.
  apply x.
Defined.
Definition hqmax : binop hq.
Proof.
  intros x y.
  generalize (hqgthorleh x y) ;
    apply sumofmaps ;
    intros H.
  apply x.
  apply y.
Defined.

Lemma hqmax_case_strong :
  Π (P : hq → UU) (x y : hq),
  (y <= x → P x) → (x <= y → P y)
  → P (hqmax x y).
Proof.
  intros P x y Hx Hy.
  unfold hqmax.
  induction (hqgthorleh x y) as [ H | H ].
  - apply Hx, hqlthtoleh, H.
  - apply Hy, H.
Qed.
Lemma hqmax_case :
  Π (P : hq → UU) (x y : hq),
  P x → P y → P (hqmax x y).
Proof.
  intros P x y Hx Hy.
  apply hqmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma hqmin_case_strong :
  Π (P : hq → UU) (x y : hq),
  (x <= y → P x) → (y <= x → P y)
  → P (hqmin x y).
Proof.
  intros P x y Hx Hy.
  unfold hqmin.
  induction (hqgthorleh x y) as [ H | H ].
  - apply Hy, hqlthtoleh, H.
  - apply Hx, H.
Qed.
Lemma hqmin_case :
  Π (P : hq → UU) (x y : hq),
  P x → P y → P (hqmin x y).
Proof.
  intros P x y Hx Hy.
  apply hqmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma hqmaxopp_opphqmin :
  Π x y : hq, hqmax (- x) (- y) = - hqmin x y.
Proof.
  intros x y.
  apply hqmax_case_strong ; intros Hxy ;
  apply hqmin_case_strong ; intros Hxy'.
  - reflexivity.
  - apply isantisymmhqleh.
    + apply neghqgthtoleh.
      intros H.
      apply Hxy', hqgth_opp'.
      exact H.
    + exact Hxy.
  - apply isantisymmhqleh.
    + apply neghqgthtoleh.
      intros H.
      apply Hxy', hqgth_opp'.
      exact H.
    + exact Hxy.
  - reflexivity.
Qed.

Lemma isassoc_hqmin : isassoc hqmin.
Proof.
  intros x y z.
  unfold hqmin.
  induction (hqgthorleh x y) as [Hxy | Hxy].
  - change (sumofmaps (λ _ : x > y, y) (λ _ : x <= y, x) (ii1 Hxy)) with y.
    induction (hqgthorleh y z) as [Hyz | Hyz].
    + change (sumofmaps (λ _ : y > z, z) (λ _ : y <= z, y) (ii1 Hyz)) with z.
      induction (hqgthorleh x z) as [Hxz | Hxz].
      * reflexivity.
      * apply fromempty.
        revert Hxz.
        apply hqgthtoneghqleh.
        apply istranshqgth with y.
        exact Hxy.
        exact Hyz.
    + change (sumofmaps (λ _ : y > z, z) (λ _ : y <= z, y) (ii2 Hyz)) with y.
      induction (hqgthorleh x y) as [Hxy' | Hxy'].
      reflexivity.
      apply fromempty.
      revert Hxy'.
      apply hqgthtoneghqleh.
      exact Hxy.
  - change (sumofmaps (λ _ : x > y, y) (λ _ : x <= y, x) (ii2 Hxy)) with x.
    induction (hqgthorleh y z) as [Hyz | Hyz].
    + change (sumofmaps (λ _ : y > z, z) (λ _ : y <= z, y) (ii1 Hyz)) with z.
      reflexivity.
    + change (sumofmaps (λ _ : y > z, z) (λ _ : y <= z, y) (ii2 Hyz)) with y.
      induction (hqgthorleh x z) as [Hxz | Hxz].
      * apply fromempty.
        revert Hxz.
        apply (hqlehtoneghqgth x z).
        apply istranshqleh with y.
        exact Hxy.
        exact Hyz.
      * induction (hqgthorleh x y) as [Hxy' | Hxy'].
        apply fromempty.
        revert Hxy'.
        apply (hqlehtoneghqgth x y).
        exact Hxy.
        reflexivity.
Qed.
Lemma iscomm_hqmin : iscomm hqmin.
Proof.
  intros x y.
  unfold hqmin.
  induction (hqgthorleh x y) as [Hxy | Hxy] ;
    induction (hqgthorleh y x) as [Hxy' | Hxy'].
  - apply fromempty.
    revert Hxy'.
    apply (hqlehtoneghqgth y x).
    apply hqlthtoleh.
    exact Hxy.
  - reflexivity.
  - reflexivity.
  - change (x = y).
    apply isantisymmhqleh.
    + exact Hxy.
    + exact Hxy'.
Qed.
Lemma isassoc_hqmax : isassoc hqmax.
Proof.
  intros x y z.
  rewrite <- (grinvinv hq x), <- (grinvinv hq y), <- (grinvinv hq z).
  change (hqmax (hqmax (- - x) (- - y)) (- - z) =
          hqmax (- - x) (hqmax (- - y) (- - z))).
  rewrite !hqmaxopp_opphqmin.
  apply maponpaths, isassoc_hqmin.
Qed.
Lemma iscomm_hqmax : iscomm hqmax.
Proof.
  intros x y.
  rewrite <- (grinvinv hq x), <- (grinvinv hq y).
  change (hqmax (- - x) (- - y) = hqmax (- - y) (- - x)).
  rewrite !hqmaxopp_opphqmin.
  apply maponpaths, iscomm_hqmin.
Qed.
Lemma isabsorb_hqmin_hqmax :
  Π x y : hq, hqmin x (hqmax x y) = x.
Proof.
  intros x y.
  unfold hqmin, hqmax.
  induction (hqgthorleh x y) as [Hxy | Hxy].
  - change (sumofmaps (λ _ : x > y, x) (λ _ : x <= y, y) (ii1 Hxy)) with x.
    induction (hqgthorleh x x) as [Hxx | Hxx].
    reflexivity.
    reflexivity.
  - change (sumofmaps (λ _ : x > y, x) (λ _ : x <= y, y) (ii2 Hxy)) with y.
    induction (hqgthorleh x y) as [Hxy' | Hxy'].
    apply fromempty.
    revert Hxy'.
    apply Hxy.
    reflexivity.
Qed.
Lemma isabsorb_hqmax_hqmin :
  Π x y : hq, hqmax x (hqmin x y) = x.
Proof.
  intros x y.
  unfold hqmin, hqmax.
  induction (hqgthorleh x y) as [Hxy | Hxy].
  - change (sumofmaps (λ _ : x > y, y) (λ _ : x <= y, x) (ii1 Hxy)) with y.
    induction (hqgthorleh x y) as [Hxy' | Hxy'].
    reflexivity.
    apply fromempty.
    revert Hxy.
    apply Hxy'.
  - change (sumofmaps (λ _ : x > y, y) (λ _ : x <= y, x) (ii2 Hxy)) with x.
    induction (hqgthorleh x x) as [Hxx | Hxx].
    reflexivity.
    reflexivity.
Qed.

Lemma islatticeop_hq :
  islatticeop hqmin hqmax.
Proof.
  repeat split.
  - exact isassoc_hqmin.
  - exact iscomm_hqmin.
  - exact isassoc_hqmax.
  - exact iscomm_hqmax.
  - exact isabsorb_hqmin_hqmax.
  - exact isabsorb_hqmax_hqmin.
Qed.

Lemma nothqlth_hqmin :
  Π x y : hq, ¬ (x < y) <-> hqmin y x = y.
Proof.
  intros x y.
  apply hqmin_case_strong ; intros H ; split ; intros H0.
  - reflexivity.
  - exact H.
  - apply isantisymmhqleh.
    exact H.
    exact H0.
  - rewrite H0.
    apply (isirreflhqgth y).
Qed.

Lemma hqmin_gt :
  Π x y z : hq, z < x → z < y → z < hqmin x y.
Proof.
  intros x y z Hx Hy.
  apply hqmin_case.
  exact Hx.
  exact Hy.
Qed.
Lemma hqmax_lt :
  Π x y z : hq, x < z → y < z → hqmax x y < z.
Proof.
  intros x y z Hx Hy.
  apply hqmax_case.
  exact Hx.
  exact Hy.
Qed.
Definition islattice_hq : islatticewithlt hq.
Proof.
  mkpair.
  exact (hqmin ,, hqmax ,, islatticeop_hq).
  mkpair.
  - mkpair.
    exact hqlth.
    split ; [ | split].
    + exact istranshqlth.
    + exact iscotranshqlth.
    + exact isirreflhqlth.
  - split ; [ | split].
    + exact nothqlth_hqmin.
    + exact hqmin_gt.
    + exact hqmax_lt.
Defined.

Lemma Lmin_hqmin :
  Lmin islattice_hq = hqmin.
Proof.
  unfold Lmin, islattice_hq.
  simpl.
  reflexivity.
Qed.
Lemma Lmax_hqmax :
  Lmax islattice_hq = hqmax.
Proof.
  unfold Lmax, islattice_hq.
  simpl.
  reflexivity.
Qed.

Lemma Lle_hqleh :
  Π x y : hq, x <= y <-> Lle islattice_hq x y.
Proof.
  intros x y.
  split.
  - intros H.
    change (hqmin x y = x).
    unfold hqmin.
    induction (hqgthorleh x y) as [ Hxy | Hxy ].
    + apply fromempty.
      revert Hxy.
      exact H.
    + reflexivity.
  - intros H.
    rewrite <- H.
    change (hqmin x y <= y).
    unfold hqmin.
    induction (hqgthorleh x y) as [Hxy | Hxy].
    + exact (isreflhqleh _).
    + exact Hxy.
Qed.

Lemma hqmax_ge_l :
  Π (x y : hq), x <= hqmax x y.
Proof.
  intros x y.
  apply_pr2 Lle_hqleh.
  rewrite <- Lmax_hqmax.
  apply (Lmax_ge_l islattice_hq).
Qed.
Lemma hqmax_ge_r :
  Π (x y : hq), y <= hqmax x y.
Proof.
  intros x y.
  apply_pr2 Lle_hqleh.
  rewrite <- Lmax_hqmax.
  apply (Lmax_ge_r islattice_hq).
Qed.
Lemma hqmax_eq_l :
  Π (x y : hq), y <= x → hqmax x y = x.
Proof.
  intros x y H.
  rewrite <- Lmax_hqmax.
  apply (Lmax_eq_l islattice_hq).
  apply Lle_hqleh.
  exact H.
Qed.
Lemma hqmax_eq_r :
  Π (x y : hq), x <= y → hqmax x y = y.
Proof.
  intros x y H.
  rewrite <- Lmax_hqmax.
  apply (Lmax_eq_r islattice_hq).
  apply Lle_hqleh.
  exact H.
Qed.
Lemma hqmax_lth_l :
  Π x y : hq, x < y <-> x < hqmax x y.
Proof.
  intros x y.
  apply hqmax_case_strong.
  - intros H ; split ; intros H0.
    + apply fromempty.
      refine (hqgehtoneghqlth _ _ _ _).
      exact H.
      exact H0.
    + apply fromempty.
      refine (isirreflhqlth _ _).
      exact H0.
  - split ; intros H0 ; exact H0.
Qed.

Lemma isrdistr_hqmax_hqplus :
  isrdistr hqmax hqplus.
Proof.
  intros x y k.
  apply hqmax_case_strong ; intros H ;
  apply hqmax_case_strong ; intros H0.
  - reflexivity.
  - apply isantisymmhqleh.
    exact H0.
    apply hqlehandplusr, H.
  - apply isantisymmhqleh.
    exact H0.
    apply hqlehandplusr, H.
  - reflexivity.
Qed.

Definition hqtminus : binop hq :=
  λ x y : hq, hqmax 0 (x - y).
Lemma istminus_hq :
  istminus (X := rngaddabgr hq) islattice_hq hqtminus.
Proof.
  unfold hqtminus.
  rewrite <- Lmax_hqmax.
  apply (abgr_tminus (X := rngaddabgr hq) islattice_hq).
  exact isrdistr_hqmax_hqplus.
Qed.

Lemma hqtminus_pos :
  Π x y : hq, x < y <-> 0 < hqtminus y x.
Proof.
  unfold hqtminus.
  intros x y ; split.
  - intros H.
    apply hqmax_lth_l.
    unfold hqminus.
    apply hqlthandplusrinv with x.
    rewrite hqplusassoc, hqlminus, hqplusl0, hqplusr0.
    exact H.
  - intros H.
    apply_pr2_in hqmax_lth_l H.
    apply hqlthandplusrinv with (- x).
    change (x - x < y - x).
    rewrite hqrminus.
    exact H.
Qed.

Definition extminus_hq : extminuswithlt (X := rngaddabgr hq) islattice_hq.
Proof.
  mkpair.
  exact (hqtminus,, istminus_hq).
  exact (λ x y : hq, pr2 (hqtminus_pos x y)).
Defined.

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
