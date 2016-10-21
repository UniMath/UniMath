(** * Archimedean property *)



(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Foundations.Algebra.Rigs_and_Rings .
Require Export UniMath.Foundations.Algebra.DivisionRig .
Require Export UniMath.Foundations.Algebra.Domains_and_Fields .
Require Export UniMath.Foundations.Algebra.ConstructiveStructures.

(** ** The standard function from the natural numbers to a monoid *)

Fixpoint natmult {X : monoid} (n : nat) (x : X) : X :=
  match n with
    | O => 0%addmonoid
    | S O => x
    | S m => (x + natmult m x)%addmonoid
  end.
Definition nattorig {X : rig} (n : nat) : X :=
  natmult (X := rigaddabmonoid X) n 1%rig.
Definition nattorng {X : rng} (n : nat) : X :=
  nattorig (X := rngtorig X) n.

Lemma natmultS :
  Π {X : monoid} (n : nat) (x : X),
    natmult (S n) x = (x + natmult n x)%addmonoid.
Proof.
  intros X n x.
  induction n as [|n].
  - now rewrite runax.
  - reflexivity.
Qed.
Lemma nattorigS {X : rig} :
  Π (n : nat), nattorig (X := X) (S n) = (1 + nattorig n)%rig.
Proof.
  intros.
  now apply (natmultS (X := rigaddabmonoid X)).
Qed.

Lemma nattorig_natmult :
  Π {X : rig} (n : nat) (x : X),
    (nattorig n * x)%rig = natmult (X := rigaddabmonoid X) n x.
Proof.
  intros.
  induction n as [|n IHn].
  - now apply rigmult0x.
  - rewrite nattorigS, natmultS.
    now rewrite rigrdistr, IHn, riglunax2.
Qed.
Lemma natmult_plus :
  Π {X : monoid} (n m : nat) (x : X),
    natmult (n + m) x = (natmult n x + natmult m x)%addmonoid.
Proof.
  induction n as [|n IHn] ; intros m x.
  - rewrite plus_O_n, lunax.
    reflexivity.
  - rewrite plus_Sn_m, !natmultS, IHn, assocax.
    reflexivity.
Qed.
Lemma nattorig_plus :
  Π {X : rig} (n m : nat),
    (nattorig (n + m) : X) = (nattorig n + nattorig m)%rig.
Proof.
  intros X n m.
  apply (natmult_plus (X := rigaddabmonoid X)).
Qed.

Lemma natmult_mult :
  Π {X : monoid} (n m : nat) (x : X),
    natmult (n * m) x = (natmult n (natmult m x))%addmonoid.
Proof.
  induction n as [|n IHn] ; intros m x.
  - reflexivity.
  - simpl (_ * _)%nat.
    assert (S n = (n + 1)%nat).
    { rewrite <- plus_n_Sm, <- plus_n_O.
      reflexivity. }
    rewrite H ; clear H.
    rewrite !natmult_plus, IHn.
    reflexivity.
Qed.
Lemma nattorig_mult :
  Π {X : rig} (n m : nat),
    (nattorig (n * m) : X) = (nattorig n * nattorig m)%rig.
Proof.
  intros X n m.
  unfold nattorig.
  rewrite (natmult_mult (X := rigaddabmonoid X)), <- nattorig_natmult.
  reflexivity.
Qed.

Lemma natmult_op {X : monoid} :
  Π (n : nat) (x y : X),
    (x + y = y + x)%addmonoid
    -> natmult n (x + y)%addmonoid = (natmult n x + natmult n y)%addmonoid.
Proof.
  intros.
  induction n as [|n IHn].
  - rewrite lunax.
    reflexivity.
  - rewrite natmultS, assocax, IHn, <- (assocax _ y).
    assert (y + natmult n x = natmult n x + y)%addmonoid.
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
  Π (n : nat) (x y : X), R x y -> R (natmult (S n) x) (natmult (S n) y).
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

Definition setquot_aux_acc {X : monoid} (R : hrel X) (x y : X) : UU :=
  Σ c : X, R (x + c)%addmonoid (y + c)%addmonoid.
Definition mk_setquot_aux_acc {X : monoid} (R : hrel X) (x y : X)
           (c : X) (Hc : R (x + c)%addmonoid (y + c)%addmonoid) : setquot_aux_acc R x y :=
  c ,, Hc.
Definition setquot_aux_val {X : monoid} {R : hrel X} {x y : X}
           (c : setquot_aux_acc R x y) : X :=
  pr1 c.
Lemma setquot_aux_pty {X : monoid} {R : hrel X} {x y : X}
      (c : setquot_aux_acc R x y) : R (x + setquot_aux_val c)%addmonoid (y + setquot_aux_val c)%addmonoid.
Proof.
  intros X R x y.
  intros c.
  exact (pr2 c).
Qed.
Definition setquot_aux {X : monoid} (R : hrel X) : hrel X :=
  λ x y : X, ∥setquot_aux_acc R x y∥.

Lemma istrans_setquot_aux {X : abmonoid} (R : hrel X) :
  istrans R -> isbinophrel R -> istrans (setquot_aux R).
Proof.
  intros X R Hr Hop.
  intros x y z.
  apply hinhfun2.
  intros c1 c2.
  simple refine (mk_setquot_aux_acc _ _ _ _ _).
  apply (setquot_aux_val c1 + setquot_aux_val c2)%addmonoid.
  refine (Hr _ _ _ _ _).
  rewrite <- assocax.
  apply (pr2 Hop).
  exact (setquot_aux_pty c1).
  rewrite assocax, (commax _ (setquot_aux_val c1)), <- !assocax.
  apply (pr2 Hop).
  exact (setquot_aux_pty c2).
Qed.
Lemma isbinophrel_setquot_aux {X : abmonoid} (R : hrel X) :
  isbinophrel R -> isbinophrel (setquot_aux R).
Proof.
  intros X R Hop.
  split.
  - intros x y z.
    apply hinhfun.
    intros c.
    simple refine (mk_setquot_aux_acc _ _ _ _ _).
    apply (setquot_aux_val c).
    rewrite !assocax.
    apply (pr1 Hop).
    exact (setquot_aux_pty c).
  - intros x y z.
    apply hinhfun.
    intros c.
    simple refine (mk_setquot_aux_acc _ _ _ _ _).
    apply (setquot_aux_val c).
    rewrite !assocax, (commax _ z), <- !assocax.
    apply (pr2 Hop).
    exact (setquot_aux_pty c).
Qed.

Lemma isequiv_setquot_aux {X : abmonoid} (R : hrel X) :
  isinvbinophrel R ->
  Π x y : X, (setquot_aux R) x y <-> R x y.
Proof.
  intros X R H x y.
  split.
  apply hinhuniv.
  intros c.
  generalize (setquot_aux_pty c).
  apply (pr2 H).
  intros H1.
  apply hinhpr.
  simple refine (mk_setquot_aux_acc _ _ _ _ _).
  apply 0%addmonoid.
  rewrite !runax.
  exact H1.
Qed.

(** ** Archimedean property in a monoid *)

Definition isarchmonoid_1_acc {X : abmonoid} (R : hrel X) (x y1 y2 : X) : UU :=
  Σ n : nat, R (natmult n y1 + x)%addmonoid (natmult n y2).
Definition mk_isarchmonoid_1_acc {X : abmonoid} (R : hrel X) (x y1 y2 : X)
           (n : nat) (Hn : R (natmult n y1 + x)%addmonoid (natmult n y2)) : isarchmonoid_1_acc R x y1 y2 :=
  n ,, Hn.
Definition isarchmonoid_1_val {X : abmonoid} {R : hrel X} {x y1 y2 : X}
           (n : isarchmonoid_1_acc R x y1 y2) : nat :=
  pr1 n.
Lemma isarchmonoid_1_pty {X : abmonoid} {R : hrel X} {x y1 y2 : X}
      (n : isarchmonoid_1_acc R x y1 y2) :
  R (natmult (isarchmonoid_1_val n) y1 + x)%addmonoid (natmult (isarchmonoid_1_val n) y2).
Proof.
  intros X R x y1 y2.
  intros n.
  exact (pr2 n).
Qed.

Definition isarchmonoid_2_acc {X : abmonoid} (R : hrel X) (x y1 y2 : X) : UU :=
  Σ n : nat, R (natmult n y1) (natmult n y2 + x)%addmonoid.
Definition mk_isarchmonoid_2_acc {X : abmonoid} (R : hrel X) (x y1 y2 : X)
           (n : nat) (Hn : R (natmult n y1) (natmult n y2 + x)%addmonoid) : isarchmonoid_2_acc R x y1 y2 :=
  n ,, Hn.
Definition isarchmonoid_2_val {X : abmonoid} {R : hrel X} {x y1 y2 : X}
           (n : isarchmonoid_2_acc R x y1 y2) : nat :=
  pr1 n.
Lemma isarchmonoid_2_pty {X : abmonoid} {R : hrel X} {x y1 y2 : X}
      (n : isarchmonoid_2_acc R x y1 y2) : R (natmult (isarchmonoid_2_val n) y1) (natmult (isarchmonoid_2_val n) y2 + x)%addmonoid.
Proof.
  intros X R x y1 y2.
  intros n.
  exact (pr2 n).
Qed.

Definition isarchmonoid {X : abmonoid} (R : hrel X) :=
  Π (x y1 y2 : X),
  R y1 y2 ->
  ∥ isarchmonoid_1_acc R x y1 y2 ∥
    × ∥ isarchmonoid_2_acc R x y1 y2 ∥.

Definition isarchmonoid_1 {X : abmonoid} (R : hrel X) :
  isarchmonoid R ->
  Π (x y1 y2 : X),
  R y1 y2 ->
  ∥ isarchmonoid_1_acc R x y1 y2 ∥ :=
  λ H x y1 y2 Hy, (pr1 (H x y1 y2 Hy)).
Definition isarchmonoid_2 {X : abmonoid} (R : hrel X) :
  isarchmonoid R ->
  Π x y1 y2 : X,
    R y1 y2 ->
    ∥ isarchmonoid_2_acc R x y1 y2 ∥ :=
  λ H x y1 y2 Hy, (pr2 (H x y1 y2 Hy)).

(** ** Archimedean property in a group *)

Definition isarchgr_acc {X : abgr} (R : hrel X) (x y1 y2 : X) : UU :=
  Σ n : nat, R (natmult n y1 + x)%addmonoid (natmult n y2).
Definition mk_isarchgr_acc {X : abgr} (R : hrel X) (x y1 y2 : X)
           (n : nat) (Hn : R (natmult n y1 + x)%addmonoid (natmult n y2)) : isarchgr_acc R x y1 y2 :=
  n ,, Hn.
Definition isarchgr_val {X : abgr} {R : hrel X} {x y1 y2 : X}
           (n : isarchgr_acc R x y1 y2) : nat :=
  pr1 n.
Lemma isarchgr_pty {X : abgr} {R : hrel X} {x y1 y2 : X}
      (n : isarchgr_acc R x y1 y2) :
  R (natmult (isarchgr_val n) y1 + x)%addmonoid (natmult (isarchgr_val n) y2).
Proof.
  intros X R x y1 y2.
  intros n.
  exact (pr2 n).
Qed.

Definition isarchgr {X : abgr} (R : hrel X) :=
  Π (x y1 y2 : X),
  R y1 y2 ->
  ∥ isarchgr_acc R x y1 y2 ∥.

Local Lemma isarchgr_isarchmonoid_aux {X : abgr} (R : hrel X) :
  isbinophrel R ->
  Π (n : nat) (x y1 y2 : X),
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
  - generalize (H x y1 y2 Hy).
    apply hinhfun.
    intros n.
    simple refine (mk_isarchmonoid_1_acc _ _ _ _ _ _).
    exact (isarchgr_val n).
    exact (isarchgr_pty n).
  - generalize (H (grinv X x) _ _ Hy).
    apply hinhfun.
    intros n.
    simple refine (mk_isarchmonoid_2_acc _ _ _ _ _ _).
    exact (isarchgr_val n).
    apply isarchgr_isarchmonoid_aux.
    exact Hop.
    exact (isarchgr_pty n).
Defined.

Lemma isarchmonoid_isarchgr {X : abgr} (R : hrel X) :
  isarchmonoid (X := abgrtoabmonoid X) R ->
  isarchgr R.
Proof.
  intros X R H x y1 y2 Hy.
  generalize (isarchmonoid_1 _ H x y1 y2 Hy).
  apply hinhfun.
  intros n.
  simple refine (mk_isarchgr_acc _ _ _ _ _ _).
  exact (isarchmonoid_1_val n).
  exact (isarchmonoid_1_pty n).
Defined.


Local Lemma isarchabgrfrac_aux {X : abmonoid} (R : hrel X)
      (Hr : isbinophrel R)
      (Hr' : istrans R)
      (y1 y2 x : abmonoiddirprod X X)
      (n1 : nat)
      (Hn1 : setquot_aux R (natmult n1 (pr1 y1 * pr2 y2) * pr1 x)%multmonoid
                         (natmult n1 (pr1 y2 * pr2 y1)%multmonoid))
      (n2 : nat)
      (Hn2 : setquot_aux R (natmult n2 (pr1 y1 * pr2 y2)%multmonoid)
                         (natmult n2 (pr1 y2 * pr2 y1) * pr2 x)%multmonoid) :
  abgrfracrel X Hr
              (natmult (X := abgrfrac X) (n1 + n2) (setquotpr (binopeqrelabgrfrac X) y1) *
               setquotpr (binopeqrelabgrfrac X) x)%multmonoid
              (natmult (X := abgrfrac X) (n1 + n2) (setquotpr (binopeqrelabgrfrac X) y2)).
Proof.
  intros.
  assert (H0 : Π n y, natmult (X := abgrfrac X) n (setquotpr (binopeqrelabgrfrac X) y) = setquotpr (binopeqrelabgrfrac X) (natmult n (pr1 y) ,, natmult n (pr2 y))).
  { intros n y.
    induction n as [|n IHn].
    reflexivity.
    rewrite !natmultS, IHn.
    reflexivity. }
  rewrite !H0.
  revert Hn1 Hn2.
  apply hinhfun2 ; simpl.
  intros c1 c2.
  set (c1_val := setquot_aux_val c1) ;
    set (c2_val := setquot_aux_val c2).
  exists (c1_val * c2_val)%multmonoid.
  set (tmp1 := (natmult (n1 + n2) (pr1 y1) * pr1 x * natmult (n1 + n2) (pr2 y2) * (c1_val * c2_val))%multmonoid).
  set (tmp2 := (natmult (n1 + n2) (pr1 y2) * (natmult (n1 + n2) (pr2 y1) * pr2 x) * (c1_val * c2_val))%multmonoid).
  change (R tmp1 tmp2).
  eapply Hr'.
  - assert (Hrw : (tmp1 = (natmult n1 (pr1 y1 * pr2 y2) * pr1 x * c1_val) * (natmult n2 (pr1 y1 * pr2 y2) * c2_val))%multmonoid).
    { unfold tmp1.
      rewrite !natmult_op, !natmult_plus, !assocax.
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
    rewrite Hrw ; clear Hrw.
    apply (pr2 Hr).
    exact (setquot_aux_pty c1).
  - assert (Hrw : (tmp2 = (natmult n1 (pr1 y2 * pr2 y1) * c1_val) * (natmult n2 (pr1 y2 * pr2 y1) * pr2 x * c2_val))%multmonoid).
    { unfold tmp2.
      rewrite !natmult_op, !natmult_plus, !assocax.
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
    rewrite Hrw ; clear Hrw.
    apply (pr1 Hr).
    exact (setquot_aux_pty c2).
Qed.
Lemma isarchabgrfrac {X : abmonoid} (R : hrel X)  (Hr : isbinophrel R) :
  istrans R ->
  isarchmonoid (setquot_aux R) ->
  isarchgr (X := abgrfrac X) (abgrfracrel X (L := R) Hr).
Proof.
  intros X R Hr Hr' H.
  simple refine (setquotuniv3prop _ (λ x y1 y2, (abgrfracrel X Hr y1 y2 ->
    ∥ isarchgr_acc (X := abgrfrac X) (abgrfracrel X Hr) x y1 y2 ∥) ,, _) _).
  abstract apply isapropimpl, propproperty.
  intros x y1 y2 Hy.
  eapply hinhfun2.

  Focus 2.
  apply (isarchmonoid_1 _ H (pr1 x) (pr1 y1 * pr2 y2)%multmonoid (pr1 y2 * pr2 y1)%multmonoid).
  revert Hy.
  apply hinhfun.
  intros n.
  simple refine (mk_setquot_aux_acc _ _ _ _ _).
  exact (pr1 n).
  exact (pr2 n).

  Focus 2.
  apply (isarchmonoid_2 _ H (pr2 x) (pr1 y1 * pr2 y2)%multmonoid (pr1 y2 * pr2 y1)%multmonoid).
  revert Hy.
  apply hinhfun.
  intros n.
  simple refine (mk_setquot_aux_acc _ _ _ _ _).
  exact (pr1 n).
  exact (pr2 n).

  intros n1 n2.
  simple refine (mk_isarchgr_acc _ _ _ _ _ _).
  exact (isarchmonoid_1_val n1 + isarchmonoid_2_val n2)%nat.
  apply (isarchabgrfrac_aux (X := X)).
  exact Hr'.
  exact (isarchmonoid_1_pty n1).
  exact (isarchmonoid_2_pty n2).
Defined.

(** ** Archimedean property in a rig *)

Definition isarchrig {X : rig} (R : hrel X) :=
  (Π y1 y2 : X, R y1 y2 -> ∃ n : nat, R (nattorig n * y1)%rig (1 + nattorig n * y2)%rig)
    × (Π x : X, ∃ n : nat, R (nattorig n) x)
    × (Π x : X, ∃ n : nat, R (nattorig n + x)%rig 0%rig).

Definition isarchrig_1 {X : rig} (R : hrel X) :
  isarchrig R ->
  Π y1 y2 : X, R y1 y2 -> ∃ n : nat, R (nattorig n * y1)%rig (1 + nattorig n * y2)%rig :=
  pr1.
Definition isarchrig_2 {X : rig} (R : hrel X) :
  isarchrig R ->
  Π x : X, ∃ n : nat, R (nattorig n) x :=
  λ H, (pr1 (pr2 H)).
Definition isarchrig_3 {X : rig} (R : hrel X) :
  isarchrig R ->
  Π x : X, ∃ n : nat, R (nattorig n + x)%rig 0%rig :=

  λ H, (pr2 (pr2 H)).

Local Lemma isarchrig_isarchmonoid_1_aux {X : rig} (R : hrel X)
      (Hr1 : R 1%rig 0%rig)
      (Hr : istrans R)
      (Hop1 : isbinophrel (X := rigaddabmonoid X) R)
      (x y1 y2 : rigaddabmonoid X)
      (m : nat)
      (Hm : R (nattorig m * y1)%rng (1%rig + nattorig m * y2)%rng)
      (n : nat)
      (Hn : R (nattorig n + x)%rng 0%rig) :
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
      (Hm : R (nattorig m * y1)%rng (1%rig + nattorig m * y2)%rng)
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
  - generalize (isarchrig_1 _ H _ _ Hy) (isarchrig_3 _ H x).
    apply hinhfun2.
    intros m n.
    simple refine (mk_isarchmonoid_1_acc _ _ _ _ _ _).
    exact (max 1 (pr1 n) * (pr1 m))%nat.
    apply isarchrig_isarchmonoid_1_aux.
    exact Hr1.
    exact Hr.
    exact Hop1.
    exact (pr2 m).
    exact (pr2 n).
  - generalize (isarchrig_1 _ H _ _ Hy) (isarchrig_2 _ H x).
    apply hinhfun2.
    intros m n.
    simple refine (mk_isarchmonoid_2_acc _ _ _ _ _ _).
    exact (max 1 (pr1 n) * (pr1 m))%nat.
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
    exists (isarchmonoid_2_val n).
    abstract (rewrite !nattorig_natmult, rigcomm1 ;
               exact (isarchmonoid_2_pty n)).
  - intros x.
    generalize (isarchmonoid_2 _ H x _ _ H01).
    apply hinhfun.
    intros n.
    exists (isarchmonoid_2_val n).
    abstract (
        tryif primitive_projections
        then pattern x at 1
        else pattern x at 2;
        rewrite <- (riglunax1 X x) ;
        tryif primitive_projections
        then pattern (0%rig : X) at 1
        else pattern (0%rig : X) at 2 ;
        rewrite <- (rigmultx0 X (nattorig (isarchmonoid_2_val n))) ;
        rewrite nattorig_natmult ;
        exact (isarchmonoid_2_pty n)).
  - intros x.
    generalize (isarchmonoid_1 _ H x _ _ H01).
    apply hinhfun.
    intros n.
    exists (isarchmonoid_1_val n).
    abstract (
        tryif primitive_projections
        then pattern (0%rig : X) at 1
        else pattern (0%rig : X) at 2;
        rewrite <- (rigmultx0 X (nattorig (isarchmonoid_1_val n))), nattorig_natmult ;
        exact (isarchmonoid_1_pty n)).
Defined.

(** ** Archimedean property in a ring *)

Definition isarchrng {X : rng} (R : hrel X) :=
  (Π x : X, R x 0%rng -> ∃ n : nat, R (nattorng n * x)%rng 1%rng)
    × (Π x : X, ∃ n : nat, R (nattorng n) x).

Definition isarchrng_1 {X : rng} (R : hrel X) :
  isarchrng R ->
  Π x : X, R x 0%rng -> ∃ n : nat, R (nattorng n * x)%rng 1%rng := pr1.
Definition isarchrng_2 {X : rng} (R : hrel X) :
  isarchrng R ->
  Π x : X, ∃ n : nat, R (nattorng n) x := pr2.

Lemma isarchrng_isarchrig {X : rng} (R : hrel X) :
  isbinophrel (X := rigaddabmonoid X) R ->
  isarchrng R -> isarchrig (X := rngtorig X) R.
Proof.
  intros X R Hop1 H.
  repeat split.
  - intros y1 y2 Hy.
    assert (R (y1 - y2)%rng 0%rng).
    abstract (apply (pr2 (isinvbinophrelgr X Hop1)) with y2 ;
               change BinaryOperations.op with (@BinaryOperations.op1 X) ;
               rewrite rngassoc1, rnglinvax1, rnglunax1, rngrunax1 ;
               exact Hy).
    generalize (isarchrng_1 _ H _ X0).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract
      (rewrite <- (rngrunax1 _ (nattorig (pr1 n) * y1)%rng), <- (rnglinvax1 _ (nattorig (pr1 n) * y2)%rng), <- rngassoc1 ;
        apply (pr2 Hop1) ;
        rewrite <- rngrmultminus, <- rngldistr ;
        exact (pr2 n)).
  - apply isarchrng_2.
    exact H.
  - intros x.
    generalize (isarchrng_2 _ H (- x)%rng).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    abstract (change 0%rig with (0%rng : X) ;
               rewrite <- (rnglinvax1 _ x) ;
               apply (pr2 Hop1) ;
               exact (pr2 n)).
Defined.

Lemma isarchrig_isarchrng {X : rng} (R : hrel X) :
  isbinophrel (X := rigaddabmonoid X) R ->
  isarchrig (X := rngtorig X) R -> isarchrng R.
Proof.
  intros X R Hr H.
  split.
  - intros x Hx.
    generalize (isarchrig_1 _ H _ _ Hx).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    rewrite <- (rngrunax1 _ 1%rng), <- (rngmultx0 _ (nattorng n)).
    exact Hn.
  - apply (isarchrig_2 (X := rngtorig X)).
    exact H.
Defined.

Lemma isarchrng_isarchgr {X : rng} (R : hrel X) :
  R 1%rng 0%rng ->
  istrans R ->
  isbinophrel (X := X) R ->
  isarchrng R -> isarchgr (X := X) R.
Proof.
  intros X R Hr0 Hr Hop1 H.
  apply isarchmonoid_isarchgr.
  apply (isarchrig_isarchmonoid (X := X)).
  exact Hr0.
  exact Hr.
  exact Hop1.
  now apply isarchrng_isarchrig.
Defined.

Lemma isarchgr_isarchrng {X : rng} (R : hrel X) :
  R 1%rng 0%rng ->
  istrans R ->
  isbinophrel (X := X) R ->
  isarchgr (X := X) R -> isarchrng R.
Proof.
  intros X R Hr0 Hr Hop1 H.
  apply isarchrig_isarchrng.
  exact Hop1.
  apply isarchmonoid_isarchrig.
  exact Hr0.
  now apply (isarchgr_isarchmonoid (X := X)).
Defined.

Theorem isarchrigtorng :
  Π (X : rig) (R : hrel X) (Hr : R 1%rig 0%rig)
    (Hadd : isbinophrel (X := rigaddabmonoid X) R)
    (Htra : istrans R)
    (Harch : isarchrig (setquot_aux (X := rigaddabmonoid X) R)), isarchrng (X := rigtorng X) (rigtorngrel X Hadd).
Proof.
  intros.
  apply isarchgr_isarchrng.
  abstract (apply hinhpr ; simpl ;
  exists 0%rig ; rewrite !rigrunax1 ;
  exact Hr).
  now apply (istransabgrfracrel (rigaddabmonoid X)).
  now generalize Hadd ; apply isbinopabgrfracrel.
  apply (isarchabgrfrac (X := rigaddabmonoid X)).
  exact Htra.
  apply isarchrig_isarchmonoid.
  abstract (apply hinhpr ; simpl ;
            apply (mk_setquot_aux_acc (X := rigaddabmonoid X) _ _ _ 0%rig) ;
            change (R (1 + 0)%rig (0 + 0)%rig) ;
            rewrite !(rigrunax1 X) ;
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
    2: apply (isarchrig_1 _ Harch (pr1 x) (pr2 x)).
    intros (n,Hn).
    exists n.
    assert ((nattorng (X := rigtorng X) n * setquotpr
    (binopeqrelabgrfrac (rigaddabmonoid X)) x)%rng = (setquotpr
    (binopeqrelabgrfrac (rigaddabmonoid X)) (nattorig n * pr1 x ,,
    nattorig n * pr2 x))%rng).
    { clear.
      induction n as [|n IHn].
      - rewrite !rigmult0x, rngmult0x.
        reflexivity.
      - unfold nattorng.
        rewrite !nattorigS, !rigrdistr, rngrdistr, !riglunax2, rnglunax2.
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
    generalize (isarchrig_2 _ Harch (pr1 x)) (isarchrig_3 _ Harch (pr2 x)).
    apply hinhfun2.
    intros (n1,Hn1) (n2,Hn2).
    exists (n1 + n2)%nat.
    revert Hn1 Hn2.
    assert (nattorng (X := rigtorng X) (n1 + n2) = setquotpr
    (binopeqrelabgrfrac (rigaddabmonoid X)) (nattorig (n1 + n2) ,,
    0%rig)).
    { generalize (n1 + n2) ; clear.
      induction n as [|n IHn].
      - reflexivity.
      - unfold nattorng ; rewrite !nattorigS.
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

Lemma natmult_commrngfrac {X : commrng} {S : subabmonoids} :
  Π n (x : X × S), natmult (X := commrngfrac X S) n (setquotpr (eqrelcommrngfrac X S) x) = setquotpr (eqrelcommrngfrac X S) (natmult (X := X) n (pr1 x) ,, (pr2 x)).
Proof.
  simpl ; intros X S n x.
  induction n as [|n IHn].
  - apply (iscompsetquotpr (eqrelcommrngfrac X S)).
    apply hinhpr ; simpl.
    exists (pr2 x).
    rewrite !(rngmult0x X).
    reflexivity.
  - rewrite !natmultS, IHn.
    apply (iscompsetquotpr (eqrelcommrngfrac X S)).
    apply hinhpr ; simpl.
    exists (pr2 x) ; simpl.
    rewrite <- (rngldistr X).
    rewrite (rngcomm2 X (pr1 (pr2 x))).
    rewrite !(rngassoc2 X).
    reflexivity.
Qed.

Lemma isarchcommrngfrac {X : commrng} {S : subabmonoids} (R : hrel X) Hop1 Hop2 Hs:
  R 1%rng 0%rng ->
  istrans R ->
  isarchrng R -> isarchrng (X := commrngfrac X S) (commrngfracgt X S (R := R) Hop1 Hop2 Hs).
Proof.
  intros X S R Hop1 Hop2 Hs H0 Htra Hr.
  split.
  - simple refine (setquotunivprop _ (λ _, (_,,_)) _).
    apply isapropimpl, propproperty.
    intros x Hx.
    revert Hx ; apply hinhuniv ; intros (c,Hx) ; simpl in Hx.
    rewrite !(rngmult0x X), (rngrunax2 X) in Hx.
    apply (hinhfun (X := Σ n, commrngfracgt X S Hop1 Hop2 Hs (setquotpr (eqrelcommrngfrac X S) ((nattorng n * pr1 x)%rng,, pr2 x)) 1%rng)).
    intros H.
    eexists (pr1 H).
    unfold nattorng.
    rewrite (nattorig_natmult (X := commrngfrac X S)).
    rewrite (natmult_commrngfrac (X := X) (S := S)).
    rewrite <- (nattorig_natmult (X := X)).
    now apply (pr2 H).
    generalize (isarchrng_1 _ Hr _ Hx) (isarchrng_2 _ Hr (pr1 (pr2 x) * pr1 c)%rng).
    apply hinhfun2.
    intros (m,Hm) (n,Hn).
    exists (max 1 n * m)%nat.
    destruct n ; simpl max.
    + apply hinhpr ; simpl.
      exists c.
      rewrite (rngrunax2 X), (rnglunax2 X), (rngassoc2 X).
      eapply Htra.
      exact Hm.
      eapply Htra.
      exact H0.
      exact Hn.
    + unfold nattorng.
      rewrite (nattorig_natmult (X := X)), natmult_mult.
      apply hinhpr ; simpl.
      exists c.
      change (R
                (natmult (Datatypes.S n) (natmult (X := X) m (pr1 x)) * 1 * pr1 c)%rng
                (1 * pr1 (pr2 x) * pr1 c)%rng).
      rewrite <- (nattorig_natmult (X := X)), (rngrunax2 X), (rnglunax2 X), (rngassoc2 X), (nattorig_natmult (X := X)).
      eapply Htra.
      apply (natmult_binophrel (X := X) R).
      exact Htra.
      exact Hop1.
      rewrite <- (nattorig_natmult (X := X)), (rngassoc2 X).
      exact Hm.
      exact Hn.
  - simple refine (setquotunivprop _ _ _).
    intros x.
    apply (hinhfun (X := Σ n : nat, commrngfracgt X S Hop1 Hop2 Hs
     (setquotpr (eqrelcommrngfrac X S) (nattorng n,, unel S))
     (setquotpr (eqrelcommrngfrac X S) x))).
    intros (n,Hn).
    exists n.
    unfold nattorng, nattorig.
    change 1%rig with (setquotpr (eqrelcommrngfrac X S)
                                (1%rng,, unel S)).
    rewrite (natmult_commrngfrac (X := X) (S := S) n).
    exact Hn.
    generalize (isarchrng_1 _ Hr _ (Hs (pr1 (pr2 x)) (pr2 (pr2 x)))) (isarchrng_2 _ Hr (pr1 x)%rng).
    apply hinhfun2.
    intros (m,Hm) (n,Hn).
    exists (max 1 n * m)%nat.
    destruct n ; simpl max.
    + apply hinhpr ; simpl.
      exists (pr2 x).
      apply (isrngmultgttoisrrngmultgt X).
      exact Hop1.
      exact Hop2.
      apply Hs.
      apply (pr2 (pr2 x)).
      eapply Htra.
      exact Hm.
      eapply Htra.
      exact H0.
      rewrite (rngrunax2 X).
      exact Hn.
    + apply hinhpr ; simpl.
      exists (pr2 x).
      change (n * m + m)%nat with (Datatypes.S n * m)%nat.
      unfold nattorng.
      apply (isrngmultgttoisrrngmultgt X).
      exact Hop1.
      exact Hop2.
      apply Hs.
      apply (pr2 (pr2 x)).
      rewrite (rngrunax2 X), (nattorig_natmult (X := X)), natmult_mult.
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
  Π x : X, ∃ n : nat, R (nattorng n) x.

Lemma isarchfld_isarchrng {X : fld} (R : hrel X) :
  Π (Hadd : isbinophrel (X := rigaddabmonoid X) R) ( Hmult : isrngmultgt X R)
    (Hirr : isirrefl R),
    isarchfld R -> isarchrng R.
Proof.
  intros X R Hadd Hmult Hirr H.
  split.
  - intros x Hx.
    case (fldchoice x) ; intros x'.
    + generalize (H (pr1 x')).
      apply hinhfun.
      intros n.
      exists (pr1 n).
      abstract (pattern (1%rng : X) at 1 ;
                 rewrite <- (pr1 (pr2 x')) ;
                apply (isrngmultgttoisrrngmultgt _ Hadd Hmult _ _ _ Hx (pr2 n))).
    + apply hinhpr.
      exists O.
      abstract (apply fromempty ;
                 refine (Hirr _ _) ;
                 rewrite x' in Hx ;
                 apply Hx).
  - exact H.
Defined.
Lemma isarchrng_isarchfld {X : fld} (R : hrel X) :
    isarchrng R -> isarchfld R.
Proof.
  intros X R H.
  intros x.
  apply (isarchrng_2 R H x).
Defined.

Theorem isarchfldfrac ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel X R ) ( is1 : isrngmultgt X R ) ( is2 : R 1%rng 0%rng ) ( nc : neqchoice R ) ( irr : isirrefl R ) ( tra : istrans R ) :
  isarchrng R -> isarchfld (X := fldfrac X is ) (fldfracgt _  is is0 is1 is2 nc).
Proof.
  intros.
  apply isarchrng_isarchfld.
  unfold fldfracgt.
  generalize (isarchcommrngfrac (X := X) (S := rngpossubmonoid X is1 is2) R is0 is1 (λ (c : X) (r : (rngpossubmonoid X is1 is2) c), r) is2 tra X0).
  intros.
  assert (H_f : Π n x, (weqfldfracgt_f X is is0 is1 is2 nc (nattorng n * x)%rng) = (nattorng n * weqfldfracgt_f X is is0 is1 is2 nc x)%rng).
  { clear -irr.
    intros n x.
    unfold nattorng.
    rewrite (nattorig_natmult (X := fldfrac X is)), (nattorig_natmult (X := commrngfrac X (@rngpossubmonoid X R is1 is2))).
    induction n as [|n IHn].
    - refine (pr2 (pr1 (isrngfunweqfldfracgt_f _ _ _ _ _ _ _))).
      exact irr.
    - rewrite !natmultS, <- IHn.
      refine (pr1 (pr1 (isrngfunweqfldfracgt_f _ _ _ _ _ _ _)) _ _).
      exact irr. }
  assert (H_0 : (weqfldfracgt_f X is is0 is1 is2 nc 0%rng) = 0%rng).
  { refine (pr2 (pr1 (isrngfunweqfldfracgt_f _ _ _ _ _ _ _))).
    exact irr. }
  assert (H_1 : (weqfldfracgt_f X is is0 is1 is2 nc 1%rng) = 1%rng).
  { refine (pr2 (pr2 (isrngfunweqfldfracgt_f _ _ _ _ _ _ _))).
    exact irr. }
  split.
  - intros x Hx.
    eapply hinhfun.
    2: apply (isarchrng_1 _ X1 (weqfldfracgt_f X is is0 is1 is2 nc x)).
    intros (n,Hn).
    exists n.
    rewrite H_f, H_1.
    exact Hn.
    rewrite H_0 in Hx.
    exact Hx.
  - intros x.
    eapply hinhfun.
    2: apply (isarchrng_2 _ X1 (weqfldfracgt_f X is is0 is1 is2 nc x)).
    intros (n,Hn).
    exists n.
    rewrite <- (rngrunax2 _ (nattorng n)), H_f, H_1, rngrunax2.
    exact Hn.
Defined.

(** ** Archimedean property in a constructive field *)

Definition isarchCF {X : ConstructiveField} (R : hrel X) :=
  Π x : X, ∃ n : nat, R (nattorng n) x.

Lemma isarchCF_isarchrng {X : ConstructiveField} (R : hrel X) :
  Π (Hadd : isbinophrel (X := rigaddabmonoid X) R) ( Hmult : isrngmultgt X R)
    (Hirr : isirrefl R),
    (Π x : X, R x 0%CF -> (x ≠ 0)%CF) ->
    isarchCF R -> isarchrng R.
Proof.
  intros X R Hadd Hmult Hirr H0 H.
  split.
  - intros x Hx.
    generalize (H (CFinv x (H0 _ Hx))).
    apply hinhfun.
    intros (n,Hn).
    exists n.
    change 1%rng with (1%CF : X).
    rewrite <- (islinv_CFinv x (H0 x Hx)).
    apply isrngmultgttoisrrngmultgt.
    exact Hadd.
    exact Hmult.
    exact Hx.
    exact Hn.
  - exact H.
Defined.
Lemma isarchrng_isarchCF {X : ConstructiveField} (R : hrel X) :
    isarchrng R -> isarchCF R.
Proof.
  intros X R H.
  intros x.
  apply (isarchrng_2 R H x).
Defined.
