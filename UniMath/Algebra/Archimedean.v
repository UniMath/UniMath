(** * Archimedean property *)



(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

(** Imports *)

Require Import UniMath.Algebra.Rigs_and_Rings .
Require Import UniMath.Algebra.DivisionRig .
Require Import UniMath.Algebra.Domains_and_Fields .
Require Import UniMath.Algebra.ConstructiveStructures.

Require Import UniMath.MoreFoundations.Tactics.

(** ** The standard function from the natural numbers to a monoid *)

Fixpoint natmult {X : monoid} (n : nat) (x : X) : X :=
  match n with
    | O => 0%addmonoid
    | S O => x
    | S m => (x + natmult m x)%addmonoid
  end.
Definition nattorig {X : rig} (n : nat) : X :=
  natmult (X := rigaddabmonoid X) n 1%rig.
Definition nattoring {X : ring} (n : nat) : X :=
  nattorig (X := ringtorig X) n.

Lemma natmultS :
  ∏ {X : monoid} (n : nat) (x : X),
    natmult (S n) x = (x + natmult n x)%addmonoid.
Proof.
  intros X n x.
  induction n as [|n].
  - now rewrite runax.
  - reflexivity.
Qed.
Lemma nattorigS {X : rig} :
  ∏ (n : nat), nattorig (X := X) (S n) = (1 + nattorig n)%rig.
Proof.
  intros.
  now apply (natmultS (X := rigaddabmonoid X)).
Qed.

Lemma nattorig_natmult :
  ∏ {X : rig} (n : nat) (x : X),
    (nattorig n * x)%rig = natmult (X := rigaddabmonoid X) n x.
Proof.
  intros.
  induction n as [|n IHn].
  - now apply rigmult0x.
  - rewrite nattorigS, natmultS.
    now rewrite rigrdistr, IHn, riglunax2.
Qed.
Lemma natmult_plus :
  ∏ {X : monoid} (n m : nat) (x : X),
    natmult (n + m) x = (natmult n x + natmult m x)%addmonoid.
Proof.
  induction n as [|n IHn] ; intros m x.
  - rewrite lunax.
    reflexivity.
  - change (S n + m)%nat with (S (n + m))%nat.
    rewrite !natmultS, IHn, assocax.
    reflexivity.
Qed.
Lemma nattorig_plus :
  ∏ {X : rig} (n m : nat),
    (nattorig (n + m) : X) = (nattorig n + nattorig m)%rig.
Proof.
  intros X n m.
  apply (natmult_plus (X := rigaddabmonoid X)).
Qed.

Lemma natmult_mult :
  ∏ {X : monoid} (n m : nat) (x : X),
    natmult (n * m) x = (natmult n (natmult m x))%addmonoid.
Proof.
  induction n as [|n IHn] ; intros m x.
  - reflexivity.
  - simpl (_ * _)%nat.
    assert (H : S n = (n + 1)%nat).
    { rewrite <- plus_n_Sm, natplusr0.
      reflexivity. }
    rewrite H ; clear H.
    rewrite !natmult_plus, IHn.
    reflexivity.
Qed.
Lemma nattorig_mult :
  ∏ {X : rig} (n m : nat),
    (nattorig (n * m) : X) = (nattorig n * nattorig m)%rig.
Proof.
  intros X n m.
  unfold nattorig.
  rewrite (natmult_mult (X := rigaddabmonoid X)), <- nattorig_natmult.
  reflexivity.
Qed.

Lemma natmult_op {X : monoid} :
  ∏ (n : nat) (x y : X),
    (x + y = y + x)%addmonoid
    -> natmult n (x + y)%addmonoid = (natmult n x + natmult n y)%addmonoid.
Proof.
  intros.
  induction n as [|n IHn].
  - rewrite lunax.
    reflexivity.
  - rewrite natmultS, assocax, IHn, <- (assocax _ y).
    assert (X1 : (y + natmult n x = natmult n x + y)%addmonoid).
    { clear IHn.
      induction n as [|n IHn].
      - rewrite lunax, runax.
        reflexivity.
      - rewrite !natmultS, <- assocax, <- X0, !assocax, IHn.
        reflexivity. }
    rewrite X1, assocax, <- natmultS, <- assocax, <- natmultS.
    reflexivity.
Qed.

Lemma natmult_binophrel {X : monoid} (R : hrel X) :
  istrans R -> isbinophrel R ->
  ∏ (n : nat) (x y : X), R x y -> R (natmult (S n) x) (natmult (S n) y).
Proof.
  intros X R Hr Hop n x y H.
  induction n as [|n IHn].
  exact H.
  rewrite !(natmultS (S _)).
  eapply Hr.
  apply (pr1 Hop).
  exact IHn.
  apply (pr2 Hop).
  exact H.
Qed.

(** ** relation  *)

Definition setquot_aux {X : monoid} (R : hrel X) : hrel X :=
  λ x y : X, ∃ c : X, R (x + c)%addmonoid (y + c)%addmonoid.

Lemma istrans_setquot_aux {X : abmonoid} (R : hrel X) :
  istrans R -> isbinophrel R -> istrans (setquot_aux R).
Proof.
  intros X R Hr Hop.
  intros x y z.
  apply hinhfun2.
  intros (c1,Hc1) (c2,Hc2).
  exists (c1 + c2)%addmonoid.
  eapply Hr.
  rewrite <- assocax.
  apply (pr2 Hop).
  exact Hc1.
  rewrite assocax, (commax _ c1), <- !assocax.
  apply (pr2 Hop).
  exact Hc2.
Qed.

Lemma isbinophrel_setquot_aux {X : abmonoid} (R : hrel X) :
  isbinophrel R -> isbinophrel (setquot_aux R).
Proof.
  intros X R Hop.
  split.
  - intros x y z.
    apply hinhfun.
    intros (c,Hc).
    exists c.
    rewrite !assocax.
    apply (pr1 Hop).
    exact Hc.
  - intros x y z.
    apply hinhfun.
    intros (c,Hc).
    exists c.
    rewrite !assocax, (commax _ z), <- !assocax.
    apply (pr2 Hop).
    exact Hc.
Qed.

Lemma isequiv_setquot_aux {X : abmonoid} (R : hrel X) :
  isinvbinophrel R ->
  ∏ x y : X, (setquot_aux R) x y <-> R x y.
Proof.
  intros X R H x y.
  split.
  apply hinhuniv.
  intros (c,H').
  generalize H'; clear H'.
  apply (pr2 H).
  intros H1.
  apply hinhpr.
  exists 0%addmonoid.
  rewrite !runax.
  exact H1.
Qed.

(** ** Archimedean property in a monoid *)

Definition isarchmonoid {X : abmonoid} (R : hrel X) :=
  ∏ x y1 y2 : X,
    R y1 y2 ->
    (∃ n : nat, R (natmult n y1 + x)%addmonoid (natmult n y2))
      × (∃ n : nat, R (natmult n y1) (natmult n y2 + x)%addmonoid).

Definition isarchmonoid_1 {X : abmonoid} (R : hrel X) :
  isarchmonoid R ->
  ∏ x y1 y2 : X,
    R y1 y2 ->
    ∃ n : nat, R (natmult n y1 + x)%addmonoid (natmult n y2) :=
  λ H x y1 y2 Hy, (pr1 (H x y1 y2 Hy)).
Definition isarchmonoid_2 {X : abmonoid} (R : hrel X) :
  isarchmonoid R ->
  ∏ x y1 y2 : X,
    R y1 y2 ->
    ∃ n : nat, R (natmult n y1) (natmult n y2 + x)%addmonoid :=
  λ H x y1 y2 Hy, (pr2 (H x y1 y2 Hy)).

(** ** Archimedean property in a group *)

Definition isarchgr {X : abgr} (R : hrel X) :=
  ∏ x y1 y2 : X,
    R y1 y2 ->
    ∃ n : nat, R (natmult n y1 + x)%addmonoid (natmult n y2).

Local Lemma isarchgr_isarchmonoid_aux {X : abgr} (R : hrel X) :
  isbinophrel R ->
  ∏ (n : nat) (x y1 y2 : X),
    R (natmult n y1 * grinv X x)%multmonoid (natmult n y2) -> R (natmult n y1) (natmult n y2 * x)%multmonoid.
Proof.
  intros X R Hop.
  intros n x y1 y2 Hy.
  apply (pr2 (isinvbinophrelgr _ Hop) _ _ (grinv X x)).
  rewrite assocax, (grrinvax X), runax.
  exact Hy.
Qed.
Lemma isarchgr_isarchmonoid {X : abgr} (R : hrel X) :
  isbinophrel R ->
  isarchgr R ->
  isarchmonoid (X := abgrtoabmonoid X) R.
Proof.
  intros X R Hop H x y1 y2 Hy.
  split.
  - now apply H.
  - generalize (H (grinv X x) _ _ Hy).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    apply isarchgr_isarchmonoid_aux.
    exact Hop.
    exact Hn.
Defined.

Lemma isarchmonoid_isarchgr {X : abgr} (R : hrel X) :
  isarchmonoid (X := abgrtoabmonoid X) R ->
  isarchgr R.
Proof.
  intros X R H x y1 y2 Hy.
  apply (isarchmonoid_1 _ H x y1 y2 Hy).
Defined.


Local Lemma isarchabgrdiff_aux {X : abmonoid} (R : hrel X)
      (Hr : isbinophrel R)
      (Hr' : istrans R)
      (y1 y2 x : abmonoiddirprod X X)
      (n1 : nat)
      (Hn1 : setquot_aux R (natmult n1 (pr1 y1 * pr2 y2) * pr1 x)%multmonoid
                         (natmult n1 (pr1 y2 * pr2 y1)%multmonoid))
      (n2 : nat)
      (Hn2 : setquot_aux R (natmult n2 (pr1 y1 * pr2 y2)%multmonoid)
                         (natmult n2 (pr1 y2 * pr2 y1) * pr2 x)%multmonoid) :
  abgrdiffrel X Hr
              (natmult (X := abgrdiff X) (n1 + n2) (setquotpr (binopeqrelabgrdiff X) y1) *
               setquotpr (binopeqrelabgrdiff X) x)%multmonoid
              (natmult (X := abgrdiff X) (n1 + n2) (setquotpr (binopeqrelabgrdiff X) y2)).
Proof.
  intros.
  assert (H0 : ∏ n y, natmult (X := abgrdiff X) n (setquotpr (binopeqrelabgrdiff X) y) = setquotpr (binopeqrelabgrdiff X) (natmult n (pr1 y) ,, natmult n (pr2 y))).
  { intros n y.
    induction n as [|n IHn].
    reflexivity.
    rewrite !natmultS, IHn.
    reflexivity. }
  rewrite !H0.
  revert Hn1 Hn2.
  apply hinhfun2 ; simpl.
  intros (c1,Hc1) (c2,Hc2).
  exists (c1 * c2)%multmonoid.
  eapply Hr'.
  assert (X0 : (natmult (n1 + n2) (pr1 y1) * pr1 x * natmult (n1 + n2) (pr2 y2) * (c1 * c2) = (natmult n1 (pr1 y1 * pr2 y2) * pr1 x * c1) * (natmult n2 (pr1 y1 * pr2 y2) * c2))%multmonoid).
  { rewrite !natmult_op, !natmult_plus, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    rewrite commax, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    rewrite commax, !assocax.
    rewrite commax, !assocax.
    rewrite commax, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    reflexivity.
    apply commax.
    apply commax. }
  simpl in X0 |- *.
  rewrite X0 ; clear X0.
  apply (pr2 Hr).
  apply Hc1.
  assert (X0 : (natmult (n1 + n2) (pr1 y2) * (natmult (n1 + n2) (pr2 y1) * pr2 x) * (c1 * c2) = (natmult n1 (pr1 y2 * pr2 y1) * c1) * (natmult n2 (pr1 y2 * pr2 y1) * pr2 x * c2))%multmonoid).
  { rewrite !natmult_op, !natmult_plus, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    rewrite commax, !assocax.
    apply maponpaths.
    rewrite commax, !assocax.
    reflexivity.
    apply commax.
    apply commax. }
  simpl in X0 |- *.
  rewrite X0 ; clear X0.
  apply (pr1 Hr).
  apply Hc2.
Qed.
Lemma isarchabgrdiff {X : abmonoid} (R : hrel X)  (Hr : isbinophrel R) :
  istrans R ->
  isarchmonoid (setquot_aux R) ->
  isarchgr (X := abgrdiff X) (abgrdiffrel X (L := R) Hr).
Proof.
  intros X R Hr Hr' H.
  simple refine (setquotuniv3prop _ (λ x y1 y2, (abgrdiffrel X Hr y1 y2 ->
    ∃ n : nat, abgrdiffrel X Hr (natmult (X := abgrdiff X) n y1 * x)%multmonoid (natmult (X := abgrdiff X) n y2)) ,, _) _).
  abstract apply isapropimpl, propproperty.
  intros x y1 y2 Hy.
  eapply hinhfun2.
  2: apply (isarchmonoid_1 _ H (pr1 x) (pr1 y1 * pr2 y2)%multmonoid (pr1 y2 * pr2 y1)%multmonoid), Hy.
  2: apply (isarchmonoid_2 _ H (pr2 x) (pr1 y1 * pr2 y2)%multmonoid (pr1 y2 * pr2 y1)%multmonoid), Hy.
  intros n1 n2.
  exists (pr1 n1 + pr1 n2)%nat.
  apply isarchabgrdiff_aux.
  exact Hr'.
  exact (pr2 n1).
  exact (pr2 n2).
Defined.

(** ** Archimedean property in a rig *)

Definition isarchrig {X : rig} (R : hrel X) :=
  (∏ y1 y2 : X, R y1 y2 -> ∃ n : nat, R (nattorig n * y1)%rig (1 + nattorig n * y2)%rig)
    × (∏ x : X, ∃ n : nat, R (nattorig n) x)
    × (∏ x : X, ∃ n : nat, R (nattorig n + x)%rig 0%rig).

Definition isarchrig_diff {X : rig} (R : hrel X) :
  isarchrig R ->
  ∏ y1 y2 : X, R y1 y2 -> ∃ n : nat, R (nattorig n * y1)%rig (1 + nattorig n * y2)%rig :=
  pr1.
Definition isarchrig_gt {X : rig} (R : hrel X) :
  isarchrig R ->
  ∏ x : X, ∃ n : nat, R (nattorig n) x :=
  λ H, (pr1 (pr2 H)).
Definition isarchrig_pos {X : rig} (R : hrel X) :
  isarchrig R ->
  ∏ x : X, ∃ n : nat, R (nattorig n + x)%rig 0%rig :=

  λ H, (pr2 (pr2 H)).

Lemma isarchrig_setquot_aux {X : rig} (R : hrel X) :
  isinvbinophrel (X := rigaddabmonoid X) R
  → isarchrig R
  → isarchrig (setquot_aux (X := rigaddabmonoid X) R).
Proof.
  intros X R Hr H.
  split ; [ | split].
  - intros y1 y2.
    apply hinhuniv.
    intros Hy.
    generalize (isarchrig_diff R H y1 y2 (pr2 Hr _ _ _ (pr2 Hy))).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    apply hinhpr.
    exists 0%rig.
    rewrite runax, runax.
    exact (pr2 n).
  - intros x.
    generalize (isarchrig_gt R H x).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    apply hinhpr.
    exists 0%rig.
    rewrite runax, runax.
    exact (pr2 n).
  - intros x.
    generalize (isarchrig_pos R H x).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    apply hinhpr.
    exists 0%rig.
    rewrite runax, runax.
    exact (pr2 n).
Qed.

Local Lemma isarchrig_isarchmonoid_1_aux {X : rig} (R : hrel X)
      (Hr1 : R 1%rig 0%rig)
      (Hr : istrans R)
      (Hop1 : isbinophrel (X := rigaddabmonoid X) R)
      (x y1 y2 : rigaddabmonoid X)
      (m : nat)
      (Hm : R (nattorig m * y1)%ring (1%rig + nattorig m * y2)%ring)
      (n : nat)
      (Hn : R (nattorig n + x)%ring 0%rig) :
   R (natmult (max 1 n * m) y1 * x)%multmonoid
     (natmult (max 1 n * m) y2).
Proof.
  intros.
  rewrite !nattorig_natmult in Hm.
  destruct n.
  + rewrite riglunax1 in Hn.
    eapply Hr.
    apply (pr1 Hop1).
    exact Hn.
    rewrite runax.
    simpl.
    rewrite <- (lunax _ (natmult m y2)).
    eapply Hr.
    exact Hm.
    apply (pr2 Hop1).
    exact Hr1.
  + rewrite natmult_mult.
    simpl max.
    rewrite <- (runax _ (natmult (S n * m) y2)).
    refine (Hr _ _ _ _ _).
    apply (pr2 Hop1).
    apply natmult_binophrel.
    exact Hr.
    exact Hop1.
    exact Hm.
    rewrite rigcomm1.
    change BinaryOperations.op1 with (BinaryOperations.op (X := rigaddabmonoid X)).
    rewrite natmult_op, assocax, <- natmult_mult.
    apply (pr1 Hop1).
    exact Hn.
    apply rigcomm1.
Qed.
Local Lemma isarchrig_isarchmonoid_2_aux {X : rig} (R : hrel X)
      (Hr1 : R 1%rig 0%rig)
      (Hr : istrans R)
      (Hop1 : isbinophrel (X := rigaddabmonoid X) R)
      (x y1 y2 : rigaddabmonoid X)
      (m : nat)
      (Hm : R (nattorig m * y1)%ring (1%rig + nattorig m * y2)%ring)
      (n : nat)
      (Hn : R (nattorig n) x) :
  R (natmult (max 1 n * m) y1)
    (natmult (max 1 n * m) y2 * x)%multmonoid.
Proof.
  intros.
  rewrite !nattorig_natmult in Hm.
  destruct n.
  + eapply Hr.
    exact Hm.
    rewrite rigcomm1.
    apply (pr1 Hop1).
    eapply Hr.
    exact Hr1.
    exact Hn.
  + rewrite natmult_mult.
    eapply Hr.
    simpl max.
    apply natmult_binophrel.
    exact Hr.
    exact Hop1.
    exact Hm.
    rewrite rigcomm1.
    change BinaryOperations.op1 with (BinaryOperations.op (X := rigaddabmonoid X)).
    rewrite natmult_op, <- natmult_mult.
    apply (pr1 Hop1).
    exact Hn.
    apply rigcomm1.
Qed.
Lemma isarchrig_isarchmonoid {X : rig} (R : hrel X) :
  R 1%rig 0%rig ->
  istrans R -> isbinophrel (X := rigaddabmonoid X) R ->
  isarchrig R -> isarchmonoid (X := rigaddabmonoid X) R.
Proof.
  intros X R Hr1 Hr Hop1 H x y1 y2 Hy.
  split.
  - generalize (isarchrig_diff _ H _ _ Hy) (isarchrig_pos _ H x).
    apply hinhfun2.
    intros m n.
    exists (max 1 (pr1 n) * (pr1 m))%nat.
    apply isarchrig_isarchmonoid_1_aux.
    exact Hr1.
    exact Hr.
    exact Hop1.
    exact (pr2 m).
    exact (pr2 n).
  - generalize (isarchrig_diff _ H _ _ Hy) (isarchrig_gt _ H x).
    apply hinhfun2.
    intros m n.
    exists (max 1 (pr1 n) * (pr1 m))%nat.
    apply isarchrig_isarchmonoid_2_aux.
    exact Hr1.
    exact Hr.
    exact Hop1.
    exact (pr2 m).
    exact (pr2 n).
Defined.

Lemma isarchmonoid_isarchrig {X : rig} (R : hrel X) :
  (R 1%rig 0%rig)
  -> isarchmonoid (X := rigaddabmonoid X) R
  -> isarchrig R.
Proof.
  intros X R H01 H.
  repeat split.
  - intros y1 y2 Hy.
    generalize (isarchmonoid_2 _ H 1%rig y1 y2 Hy).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract (rewrite !nattorig_natmult, rigcomm1 ;
               exact (pr2 n)).
  - intros x.
    generalize (isarchmonoid_2 _ H x _ _ H01).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract (
        pattern x at 1;
        rewrite <- (riglunax1 X x) ;
        pattern (0%rig : X) at 1;
        rewrite <- (rigmultx0 X (nattorig (pr1 n))) ;
        rewrite nattorig_natmult ;
        exact (pr2 n)).
  - intros x.
    generalize (isarchmonoid_1 _ H x _ _ H01).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract (
        pattern (0%rig : X) at 1;
        rewrite <- (rigmultx0 X (nattorig (pr1 n))), nattorig_natmult ;
        exact (pr2 n)).
Defined.

(** ** Archimedean property in a ring *)

Definition isarchring {X : ring} (R : hrel X) :=
  (∏ x : X, R x 0%ring -> ∃ n : nat, R (nattoring n * x)%ring 1%ring)
    × (∏ x : X, ∃ n : nat, R (nattoring n) x).

Definition isarchring_1 {X : ring} (R : hrel X) :
  isarchring R ->
  ∏ x : X, R x 0%ring -> ∃ n : nat, R (nattoring n * x)%ring 1%ring := pr1.
Definition isarchring_2 {X : ring} (R : hrel X) :
  isarchring R ->
  ∏ x : X, ∃ n : nat, R (nattoring n) x := pr2.

Lemma isarchring_isarchrig {X : ring} (R : hrel X) :
  isbinophrel (X := rigaddabmonoid X) R ->
  isarchring R -> isarchrig (X := ringtorig X) R.
Proof.
  intros X R Hop1 H.
  repeat split.
  - intros y1 y2 Hy.
    assert (X0 : R (y1 - y2)%ring 0%ring).
    abstract (apply (pr2 (isinvbinophrelgr X Hop1)) with y2 ;
               change BinaryOperations.op with (@BinaryOperations.op1 X) ;
               rewrite ringassoc1, ringlinvax1, ringlunax1, ringrunax1 ;
               exact Hy).
    generalize (isarchring_1 _ H _ X0).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract
      (rewrite <- (ringrunax1 _ (nattorig (pr1 n) * y1)%ring), <- (ringlinvax1 _ (nattorig (pr1 n) * y2)%ring), <- ringassoc1 ;
        apply (pr2 Hop1) ;
        rewrite <- ringrmultminus, <- ringldistr ;
        exact (pr2 n)).
  - apply isarchring_2.
    exact H.
  - intros x.
    generalize (isarchring_2 _ H (- x)%ring).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract (change 0%rig with (0%ring : X) ;
               rewrite <- (ringlinvax1 _ x) ;
               apply (pr2 Hop1) ;
               exact (pr2 n)).
Defined.

Lemma isarchrig_isarchring {X : ring} (R : hrel X) :
  isbinophrel (X := rigaddabmonoid X) R ->
  isarchrig (X := ringtorig X) R -> isarchring R.
Proof.
  intros X R Hr H.
  split.
  - intros x Hx.
    generalize (isarchrig_diff _ H _ _ Hx).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    rewrite <- (ringrunax1 _ 1%ring), <- (ringmultx0 _ (nattoring n)).
    exact Hn.
  - apply (isarchrig_gt (X := ringtorig X)).
    exact H.
Defined.

Lemma isarchring_isarchgr {X : ring} (R : hrel X) :
  R 1%ring 0%ring ->
  istrans R ->
  isbinophrel (X := X) R ->
  isarchring R -> isarchgr (X := X) R.
Proof.
  intros X R Hr0 Hr Hop1 H.
  apply isarchmonoid_isarchgr.
  apply (isarchrig_isarchmonoid (X := X)).
  exact Hr0.
  exact Hr.
  exact Hop1.
  now apply isarchring_isarchrig.
Defined.

Lemma isarchgr_isarchring {X : ring} (R : hrel X) :
  R 1%ring 0%ring ->
  istrans R ->
  isbinophrel (X := X) R ->
  isarchgr (X := X) R -> isarchring R.
Proof.
  intros X R Hr0 Hr Hop1 H.
  apply isarchrig_isarchring.
  exact Hop1.
  apply isarchmonoid_isarchrig.
  exact Hr0.
  now apply (isarchgr_isarchmonoid (X := X)).
Defined.

Theorem isarchrigtoring :
  ∏ (X : rig) (R : hrel X) (Hr : R 1%rig 0%rig)
    (Hadd : isbinophrel (X := rigaddabmonoid X) R)
    (Htra : istrans R)
    (Harch : isarchrig (setquot_aux (X := rigaddabmonoid X) R)), isarchring (X := rigtoring X) (rigtoringrel X Hadd).
Proof.
  intros.
  apply isarchgr_isarchring.
  abstract (apply hinhpr ; simpl ;
  exists 0%rig ; rewrite !rigrunax1 ;
  exact Hr).
  now apply (istransabgrdiffrel (rigaddabmonoid X)).
  now generalize Hadd ; apply isbinopabgrdiffrel.
  apply (isarchabgrdiff (X := rigaddabmonoid X)).
  exact Htra.
  apply isarchrig_isarchmonoid.
  abstract (apply hinhpr ; simpl ;
  exists 0%rig ; rewrite !rigrunax1 ;
  exact Hr).
  (now apply (istrans_setquot_aux (X := rigaddabmonoid X))).
  (now apply (isbinophrel_setquot_aux (X := rigaddabmonoid X))).
  exact Harch.
(* Proof without (Hr : R 1%rig 0%rig)
  split.
  - intros xx Hx0.
    generalize (pr1 (pr2 xx)).
    apply hinhuniv ; intros (x,Hx).
    rewrite <- (setquotl0 _ xx (x,,Hx)) in Hx0 |- * ; simpl pr1 in Hx0 |- * ; clear xx Hx.
    eapply hinhfun.
    2: apply (isarchrig_diff _ Harch (pr1 x) (pr2 x)).
    intros (n,Hn).
    exists n.
    assert ((nattoring (X := rigtoring X) n * setquotpr
    (binopeqrelabgrdiff (rigaddabmonoid X)) x)%ring = (setquotpr
    (binopeqrelabgrdiff (rigaddabmonoid X)) (nattorig n * pr1 x ,,
    nattorig n * pr2 x))%ring).
    { clear.
      induction n as [|n IHn].
      - rewrite !rigmult0x, ringmult0x.
        reflexivity.
      - unfold nattoring.
        rewrite !nattorigS, !rigrdistr, ringrdistr, !riglunax2, ringlunax2.
        simpl.
        eapply pathscomp0.
        apply maponpaths.
        apply IHn.
        reflexivity. }
    rewrite X0 ; clear X0.
    revert Hn.
    apply hinhfun ; simpl.
    intros (c,Hc).
    exists c.
    rewrite rigrunax1.
    exact Hc.
    revert Hx0.
    apply hinhfun ; simpl.
    intros (c,Hc).
    exists c.
    rewrite riglunax1, rigrunax1 in Hc.
    exact Hc.
  - intros xx.
    generalize (pr1 (pr2 xx)).
    apply hinhuniv ; intros (x,Hx).
    rewrite <- (setquotl0 _ xx (x,,Hx)) ; simpl pr1 ; clear xx Hx.
    generalize (isarchrig_gt _ Harch (pr1 x)) (isarchrig_pos _ Harch (pr2 x)).
    apply hinhfun2.
    intros (n1,Hn1) (n2,Hn2).
    exists (n1 + n2)%nat.
    revert Hn1 Hn2.
    assert (nattoring (X := rigtoring X) (n1 + n2) = setquotpr
    (binopeqrelabgrdiff (rigaddabmonoid X)) (nattorig (n1 + n2) ,,
    0%rig)).
    { generalize (n1 + n2) ; clear.
      induction n as [|n IHn].
      - reflexivity.
      - unfold nattoring ; rewrite !nattorigS.
        rewrite <- (riglunax1 _ 0%rig).
        eapply pathscomp0.
        apply maponpaths.
        exact IHn.
        reflexivity. }
    rewrite X0 ; clear X0.
    apply hinhfun2 ; simpl.
    intros (c1,Hc1) (c2,Hc2).
    exists (c1+c2)%rig.
    eapply Htra.
    assert (nattorig (n1 + n2) + pr2 x + (c1 + c2) =
            ((nattorig n1 + c1) + (nattorig n2 + pr2 x + c2)))%rig.
    { rewrite nattorig_plus, !rigassoc1.
      apply maponpaths.
      rewrite rigcomm1, !rigassoc1.
      rewrite rigcomm1, !rigassoc1.
      apply maponpaths.
      rewrite rigcomm1, !rigassoc1.
      reflexivity. }
    simpl in X0 |- * ; rewrite X0 ; clear X0.
    apply (pr2 Hadd).
    exact Hc1.
    rewrite rigrunax1, <- rigassoc1.
    apply (pr1 Hadd).
    rewrite riglunax1 in Hc2.
    exact Hc2.*)
Defined.

Lemma natmult_commringfrac {X : commring} {S : subabmonoid _} :
  ∏ n (x : X × S), natmult (X := commringfrac X S) n (setquotpr (eqrelcommringfrac X S) x) = setquotpr (eqrelcommringfrac X S) (natmult (X := X) n (pr1 x) ,, (pr2 x)).
Proof.
  simpl ; intros X S n x.
  induction n as [|n IHn].
  - apply (iscompsetquotpr (eqrelcommringfrac X S)).
    apply hinhpr ; simpl.
    exists (pr2 x).
    rewrite !(ringmult0x X).
    reflexivity.
  - rewrite !natmultS, IHn.
    apply (iscompsetquotpr (eqrelcommringfrac X S)).
    apply hinhpr ; simpl.
    exists (pr2 x) ; simpl.
    rewrite <- (ringldistr X).
    rewrite (ringcomm2 X (pr1 (pr2 x))).
    rewrite !(ringassoc2 X).
    reflexivity.
Qed.

Lemma isarchcommringfrac {X : commring} {S : subabmonoid _} (R : hrel X) Hop1 Hop2 Hs:
  R 1%ring 0%ring ->
  istrans R ->
  isarchring R -> isarchring (X := commringfrac X S) (commringfracgt X S (R := R) Hop1 Hop2 Hs).
Proof.
  intros X S R Hop1 Hop2 Hs H0 Htra Hr.
  split.
  - simple refine (setquotunivprop _ (λ _, (_,,_)) _).
    apply isapropimpl, propproperty.
    intros x Hx.
    revert Hx ; apply hinhuniv ; intros (c,Hx) ; simpl in Hx.
    rewrite !(ringmult0x X), (ringrunax2 X) in Hx.
    apply (hinhfun (X := ∑ n, commringfracgt X S Hop1 Hop2 Hs (setquotpr (eqrelcommringfrac X S) ((nattoring n * pr1 x)%ring,, pr2 x)) 1%ring)).
    intros H.
    eexists (pr1 H).
    unfold nattoring.
    rewrite (nattorig_natmult (X := commringfrac X S)).
    rewrite (natmult_commringfrac (X := X) (S := S)).
    rewrite <- (nattorig_natmult (X := X)).
    now apply (pr2 H).
    generalize (isarchring_1 _ Hr _ Hx) (isarchring_2 _ Hr (pr1 (pr2 x) * pr1 c)%ring).
    apply hinhfun2.
    intros (m,Hm) (n,Hn).
    exists (max 1 n * m)%nat.
    destruct n ; simpl max.
    + apply hinhpr ; simpl.
      exists c.
      rewrite (ringrunax2 X), (ringlunax2 X), (ringassoc2 X).
      eapply Htra.
      exact Hm.
      eapply Htra.
      exact H0.
      exact Hn.
    + unfold nattoring.
      rewrite (nattorig_natmult (X := X)), natmult_mult.
      apply hinhpr ; simpl.
      exists c.
      change (R
                (natmult (succ n) (natmult (X := X) m (pr1 x)) * 1 * pr1 c)%ring
                (1 * pr1 (pr2 x) * pr1 c)%ring).
      rewrite <- (nattorig_natmult (X := X)), (ringrunax2 X), (ringlunax2 X), (ringassoc2 X), (nattorig_natmult (X := X)).
      eapply Htra.
      apply (natmult_binophrel (X := X) R).
      exact Htra.
      exact Hop1.
      rewrite <- (nattorig_natmult (X := X)), (ringassoc2 X).
      exact Hm.
      exact Hn.
  - simple refine (setquotunivprop _ _ _).
    intros x.
    apply (hinhfun (X := ∑ n : nat, commringfracgt X S Hop1 Hop2 Hs
     (setquotpr (eqrelcommringfrac X S) (nattoring n,, unel S))
     (setquotpr (eqrelcommringfrac X S) x))).
    intros (n,Hn).
    exists n.
    unfold nattoring, nattorig.
    change 1%rig with (setquotpr (eqrelcommringfrac X S)
                                (1%ring,, unel S)).
    rewrite (natmult_commringfrac (X := X) (S := S) n).
    exact Hn.
    generalize (isarchring_1 _ Hr _ (Hs (pr1 (pr2 x)) (pr2 (pr2 x)))) (isarchring_2 _ Hr (pr1 x)%ring).
    apply hinhfun2.
    intros (m,Hm) (n,Hn).
    exists (max 1 n * m)%nat.
    destruct n ; simpl max.
    + apply hinhpr ; simpl.
      exists (pr2 x).
      apply (isringmultgttoisrringmultgt X).
      exact Hop1.
      exact Hop2.
      apply Hs.
      apply (pr2 (pr2 x)).
      eapply Htra.
      exact Hm.
      eapply Htra.
      exact H0.
      rewrite (ringrunax2 X).
      exact Hn.
    + apply hinhpr ; simpl.
      exists (pr2 x).
      change (n * m + m)%nat with (succ n * m)%nat.
      unfold nattoring.
      apply (isringmultgttoisrringmultgt X).
      exact Hop1.
      exact Hop2.
      apply Hs.
      apply (pr2 (pr2 x)).
      rewrite (ringrunax2 X), (nattorig_natmult (X := X)), natmult_mult.
      eapply Htra.
      apply (natmult_binophrel (X := X) R).
      exact Htra.
      exact Hop1.
      rewrite <- (nattorig_natmult (X := X)).
      exact Hm.
      exact Hn.
Qed.

(** ** Archimedean property in a field *)

Definition isarchfld {X : fld} (R : hrel X) :=
  ∏ x : X, ∃ n : nat, R (nattoring n) x.

Lemma isarchfld_isarchring {X : fld} (R : hrel X) :
  ∏ (Hadd : isbinophrel (X := rigaddabmonoid X) R) ( Hmult : isringmultgt X R)
    (Hirr : isirrefl R),
    isarchfld R -> isarchring R.
Proof.
  intros X R Hadd Hmult Hirr H.
  split.
  - intros x Hx.
    case (fldchoice x) ; intros x'.
    + generalize (H (pr1 x')).
      apply hinhfun.
      intros n.
      exists (pr1 n).
      abstract (pattern (1%ring : X) at 1 ;
                 rewrite <- (pr1 (pr2 x')) ;
                apply (isringmultgttoisrringmultgt _ Hadd Hmult _ _ _ Hx (pr2 n))).
    + apply hinhpr.
      exists O.
      abstract (apply fromempty ;
                 refine (Hirr _ _) ;
                 rewrite x' in Hx ;
                 apply Hx).
  - exact H.
Defined.
Lemma isarchring_isarchfld {X : fld} (R : hrel X) :
    isarchring R -> isarchfld R.
Proof.
  intros X R H.
  intros x.
  apply (isarchring_2 R H x).
Defined.

Theorem isarchfldfrac ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel X R ) ( is1 : isringmultgt X R ) ( is2 : R 1%ring 0%ring ) ( nc : neqchoice R ) ( irr : isirrefl R ) ( tra : istrans R ) :
  isarchring R -> isarchfld (X := fldfrac X is ) (fldfracgt _  is is0 is1 is2 nc).
Proof.
  intros.
  apply isarchring_isarchfld.
  unfold fldfracgt.
  generalize (isarchcommringfrac (X := X) (S := ringpossubmonoid X is1 is2) R is0 is1 (λ (c : X) (r : (ringpossubmonoid X is1 is2) c), r) is2 tra X0).
  intros.
  assert (H_f : ∏ n x, (weqfldfracgt_f X is is0 is1 is2 nc (nattoring n * x)%ring) = (nattoring n * weqfldfracgt_f X is is0 is1 is2 nc x)%ring).
  { clear -irr.
    intros n x.
    unfold nattoring.
    rewrite (nattorig_natmult (X := fldfrac X is)), (nattorig_natmult (X := commringfrac X (@ringpossubmonoid X R is1 is2))).
    induction n as [|n IHn].
    - refine (pr2 (pr1 (isringfunweqfldfracgt_f _ _ _ _ _ _ _))).
      exact irr.
    - rewrite !natmultS, <- IHn.
      refine (pr1 (pr1 (isringfunweqfldfracgt_f _ _ _ _ _ _ _)) _ _).
      exact irr. }
  assert (H_0 : (weqfldfracgt_f X is is0 is1 is2 nc 0%ring) = 0%ring).
  { refine (pr2 (pr1 (isringfunweqfldfracgt_f _ _ _ _ _ _ _))).
    exact irr. }
  assert (H_1 : (weqfldfracgt_f X is is0 is1 is2 nc 1%ring) = 1%ring).
  { refine (pr2 (pr2 (isringfunweqfldfracgt_f _ _ _ _ _ _ _))).
    exact irr. }
  split.
  - intros x Hx.
    eapply hinhfun.
    2: apply (isarchring_1 _ X1 (weqfldfracgt_f X is is0 is1 is2 nc x)).
    intros (n,Hn).
    exists n.
    rewrite H_f, H_1.
    exact Hn.
    rewrite H_0 in Hx.
    exact Hx.
  - intros x.
    eapply hinhfun.
    2: apply (isarchring_2 _ X1 (weqfldfracgt_f X is is0 is1 is2 nc x)).
    intros (n,Hn).
    exists n.
    rewrite <- (ringrunax2 _ (nattoring n)), H_f, H_1, ringrunax2.
    exact Hn.
Defined.

(** ** Archimedean property in a constructive field *)

Definition isarchCF {X : ConstructiveField} (R : hrel X) :=
  ∏ x : X, ∃ n : nat, R (nattoring n) x.

Lemma isarchCF_isarchring {X : ConstructiveField} (R : hrel X) :
  ∏ (Hadd : isbinophrel (X := rigaddabmonoid X) R) ( Hmult : isringmultgt X R)
    (Hirr : isirrefl R),
    (∏ x : X, R x 0%CF -> (x ≠ 0)%CF) ->
    isarchCF R -> isarchring R.
Proof.
  intros X R Hadd Hmult Hirr H0 H.
  split.
  - intros x Hx.
    generalize (H (CFinv x (H0 _ Hx))).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    change 1%ring with (1%CF : X).
    rewrite <- (islinv_CFinv x (H0 x Hx)).
    apply isringmultgttoisrringmultgt.
    exact Hadd.
    exact Hmult.
    exact Hx.
    exact Hn.
  - exact H.
Defined.
Lemma isarchring_isarchCF {X : ConstructiveField} (R : hrel X) :
    isarchring R -> isarchCF R.
Proof.
  intros X R H.
  intros x.
  apply (isarchring_2 R H x).
Defined.
