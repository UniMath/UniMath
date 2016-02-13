(** * Archimedean property

*)



(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Foundations.Algebra.Rigs_and_Rings .
Require Export UniMath.Foundations.Algebra.DivisionRig .
Require Export UniMath.Foundations.Algebra.Domains_and_Fields .

(** ** Injection of natural numbers *)

Fixpoint natmult {X : monoid} (n : nat) (x : X) : X :=
  match n with
    | O => 0%addmonoid
    | S O => x
    | S m => (x + natmult m x)%addmonoid
  end.
Definition nattorig {X : rig} (n : nat) : X :=
  natmult (X := rigaddabmonoid X) n 1%rig.

Lemma natmultS :
  ∀ {X : monoid} (n : nat) (x : X),
    natmult (S n) x = (x + natmult n x)%addmonoid.
Proof.
  intros X [ | n] x.
  - now rewrite runax.
  - reflexivity.
Qed.
Lemma nattorigS {X : rig} :
  ∀ (n : nat), nattorig (X := X) (S n) = (1 + nattorig n)%rig.
Proof.
  intros.
  now apply (natmultS (X := rigaddabmonoid X)).
Qed.

Lemma natmult_ext :
  ∀ (X : hSet) (op op' : binop X) (is : ismonoidop op) (is' : ismonoidop op'),
  ∀ (x : (((X,,op),,is) : monoid)) (x' : (((X,,op'),,is') : monoid)) (n : nat),
    x = x' -> (unel_is is = unel_is is') -> (∀ y y', op y y' = op' y y')
    -> natmult n x = natmult n x'.
Proof.
  intros.
  induction n.
  - apply X1.
  - rewrite !natmultS.
    rewrite IHn, X0.
    apply X2.
Qed.

Lemma nattorig_natmult :
  ∀ {X : rig} (n : nat) (x : X),
    (nattorig n * x)%rig = natmult (X := rigaddabmonoid X) n x.
Proof.
  intros.
  induction n.
  - now apply rigmult0x.
  - rewrite nattorigS, natmultS.
    now rewrite rigrdistr, IHn, riglunax2.
Qed.

(** ** Definition of archimedean property *)

Definition isarchmonoid (X : monoid) (R : hrel X) :=
  ∀ x y : X, R y 0%addmonoid -> ∃ n : nat, R (natmult n y) x.
Definition isarchrig (X : rig) (R : hrel X) :=
  isarchmonoid (rigaddabmonoid X) R.
Definition isarchrng (X : rng) (R : hrel X) :=
  isarchrig X R.
Definition isarchfld (X : fld) (R : hrel X) :=
  isarchrng X R.

Definition isarchfld' (X : fld) (R : hrel X) :=
  ∀ x : X, ∃ n : nat, R (nattorig (X := pr1fld X) n) x.

Lemma isarchfld_isarchfld' :
  ∀ (X : fld) (R : hrel X) (Hr10 : R 1%rng 0%rng)
    (is : isarchfld X R), isarchfld' X R.
Proof.
  intros.
  intros x.
  apply (is x (1%rng : X)).
  exact Hr10.
Qed.
Lemma isarchfld'_isarchfld :
  ∀ (X : fld) (R : hrel X)
    (Hadd : isbinophrel (X := rigaddabmonoid X) R) ( Hmult : isrngmultgt X R )
    (Hirr : isirrefl R)
    (is : isarchfld' X R), isarchfld X R.
Proof.
  intros.
  intros x y Hy.
  assert (Hy0 : y != (0%rng : X)).
  { simple refine (rtoneq _ _).
    exact R.
    exact Hirr.
    exact Hy. }
  generalize (is (x * (fldmultinv y Hy0))%rng).
  apply hinhfun.
  intros n.
  exists (pr1 n).
  pattern x at 2 ;
    rewrite <- (rngrunax2 _ x), <- (rngrunax2 _ (natmult (pr1 n) y)).
  generalize (pr1 (pr2 (fldmultinvpair X y Hy0))).
  change (((fldmultinv y Hy0) * y)%rng = (1%rng : X) ->
          R (natmult (pr1 n) y * (1 : X))%rng (x * (1 : X))%rng).
  intros <-.
  change (R (natmult (pr1 n) y * (fldmultinv y Hy0 * y))%rng
            (x * (fldmultinv y Hy0 * y))%rng).
  rewrite <- !(rngassoc2 (pr1fld X)).
  apply isrngmultgttoisrrngmultgt.
  exact Hadd.
  exact Hmult.
  exact Hy.
  rewrite <- nattorig_natmult, (rngassoc2 (pr1fld X)).
  generalize (pr2 (pr2 (fldmultinvpair X y Hy0))).
  change ((y * (fldmultinv y Hy0))%rng = (1%rng : X) ->
   R (nattorig (pr1 n) * (y * fldmultinv y Hy0))%rng
     (x * fldmultinv y Hy0)%rng).
  intros ->.
  rewrite (rngrunax2 (pr1fld X)).
  exact (pr2 n).
Qed.

Definition ex_partial_minus (X : rig) (R : hrel X) :=
   ∀ x y : X, R x y -> ∃ z : X, R z 0%rig × x = (y + z)%rig.

Definition ex_partial_minus_week (X : rig) (R : hrel X) :=
  ∀ (n : nat) (x y : X),
    (∃ c, R (x + c)%rig (y + c)%rig)
    -> ∃ m c, R (nattorig m * x + c)%rig (nattorig n + nattorig m * y + c)%rig.

Lemma ex_partal_minus_imply_week {X : rig} (R : hrel X)
      (R10 : R 1%rig 0%rig) (Htra : istrans R)
      (Hadd : isbinophrel (X := rigaddabmonoid X) R)
      (Harch : isarchrig X R)
      (Hminus : ex_partial_minus X R) :
  ex_partial_minus_week X R.
Proof.
  intros.
  intros n x y.
  apply hinhuniv.
  intros (c,Hc).
  destruct n.
  - apply hinhpr.
    exists 1, c.
    now rewrite !nattorig_natmult, riglunax1.
  - assert (R (nattorig (S n)) 0%rig).
    { induction n.
      exact R10.
      rewrite nattorigS.
      refine (Htra _ _ _ _ _).
      apply (pr1 Hadd).
      exact IHn.
      simpl op.
      now rewrite rigrunax1. }
    generalize (Hminus _ _ Hc).
    apply hinhuniv.
    intros (z,(Hz0,Hz)).
    generalize (Harch (nattorig (S n)) _ Hz0).
    apply hinhfun.
    intros (m,Hm).
    exists m.
    exists (nattorig m * c)%rig.
    rewrite <- rigldistr, Hz, !rigldistr, rigcomm1, rigassoc1.
    apply (pr2 Hadd).
    now rewrite nattorig_natmult.
Qed.

Theorem isarchrigtorng_gt :
  ∀ (X : rig) (R : hrel X)
    (Hpos : ∀ x : X, ∃ c : X, R (x + c)%rig 0%rig)
    (Hminus : ex_partial_minus_week X R)
    (Hadd : isbinophrel (X := rigaddabmonoid X) R)
    (R10 : R 1%rig 0%rig)
    (Htra : istrans R)
    (Harch : isarchrig X R), isarchrng (rigtorng X) (rigtorngrel X Hadd).
Proof.
  intros.
  intros x y Hy.

  assert (H : ∀ n : nat, nattorig (X := rigtorng X) n = setquotpr (binopeqrelabgrfrac (rigaddabmonoid X)) (nattorig n ,, 0%rig)).
  { clear.
    induction n.
    reflexivity.
    rewrite <- (rigrunax1 _ 0%rig).
    rewrite !nattorigS, IHn.
    unfold op1 ; simpl.
    unfold rigtorngop1 ; simpl.
    apply (setquotfun2comm (eqrelabgrfrac (rigaddabmonoid X)) (eqrelabgrfrac (rigaddabmonoid X))). }

  assert (H0 : ∃ n : nat, rigtorngrel X Hadd (nattorig (X := rigtorng X) n) (x - y)%rng).
  { generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
    apply hinhuniv2.
    intros x' y'.
    revert Hy.
    rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
    destruct x' as [(x1,x2) Hx'].
    destruct y' as [(y1,y2) Hy'].
    simpl pr1 ; simpl pr2.
    clear x y Hx' Hy'.
    intros Hy.
    generalize (Hpos (x2 + y1)%rig).
    apply hinhuniv.
    intros (c,Hc).
    generalize (Harch (x1 + y2 + c)%rig _ R10).
    apply hinhfun ; intros (n,Hn).
    exists n.
    rewrite H ; simpl.
    apply hinhpr ; simpl.
    exists c.
    rewrite rigassoc1, rigrunax1, <- (rigrunax1 _ (x1 + y2 + c)%rng).
    refine (Htra _ _ _ _ _).
    apply (pr1 Hadd), Hc.
    apply (pr2 Hadd), Hn. }

  assert (H1 : ∀ n : nat, ∃ m : nat, rigtorngrel X Hadd (natmult (X := rigaddabmonoid (rigtorng X)) m y) (nattorig (X := rigtorng X) n)%rng).
  { intros n.
    generalize (pr1 (pr2 y)).
    apply hinhuniv.
    intros y' ; revert Hy.
    rewrite <- (setquotl0 _ y y').
    destruct y' as [(y1,y2) Hy'].
    simpl pr1 ; simpl pr2.
    apply hinhuniv ; simpl op.
    intros (c,Hc).
    rewrite rigrunax1, riglunax1 in Hc.
    refine (hinhfun _ _).
    2: apply (Hminus n y1 y2).
    intros (m,(d,Hd)).
    exists m.
    rewrite <- nattorig_natmult, !H.
    apply hinhpr.
    simpl op.
    exists d.
    rewrite !rigmult0x, !rigrunax1.
    apply Hd.
    apply hinhpr.
    now exists c. }

  revert H0.
  apply hinhuniv.
  intros n.
  specialize (H1 (pr1 n)).
  revert H1.
  apply hinhfun.
  intros m.
  exists (S (pr1 m)).
  simple refine (istransabgrfracrel _ _ _ _ _ _ _ _).
  apply Htra.
  apply (nattorig (pr1 n) + y)%rng.
  rewrite natmultS, <- nattorig_natmult.
  simpl op.
  rewrite (rigcomm1 (rigtorng X)).
  apply (pr2 (isbinopabgrfracrel (rigaddabmonoid X) Hadd)).
  generalize (pr2 m).
  now rewrite <- nattorig_natmult.
  simple refine (pr2 (isinvbinophrelgr (rngaddabgr (rigtorng X)) _) _ _ (- y)%rng _).
  apply (isbinopabgrfracrel (rigaddabmonoid X) Hadd).
  change (rigtorngrel X Hadd (nattorig (X := rigtorng X) (pr1 n) + y + - y)%rng (x - y)%rng).
  rewrite (rngassoc1 (rigtorng X)), rngrinvax1, rngrunax1.
  apply (pr2 n).
Qed.

Theorem isarchfldfrac' ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1%rng 0%rng ) ( nc : neqchoice R ) ( asy : isasymm R ) : isarchrig X R -> isarchfld' (fldfrac X is ) (fldfracgt _  is is0 is1 is2 nc).
Proof.
  intros.
  intros x.
  set ( P := fun z => ∃ n : nat, fldfracgt X is is0 is1 is2 nc (nattorig (X := pr1fld (fldfrac X is)) n) z ) .
  set ( P' := fun z' => ∃ n : nat, commrngfracgt X ( rngpossubmonoid X is1 is2 ) is0 is1 ( fun c r => r )  ( weqfldfracgt_f X is is0 is1 is2 nc ( tofldfrac X is (nattorig (X := pr1intdom X) n) ) ) z' )  .
  assert ( e : forall z : fldfrac X is , P z = P' ( weqfldfracgt_f X is is0 is1 is2 nc z ) ) .
  { intro zz.
    unfold P, P'.
    apply maponpaths.
    apply maponpaths.
    apply funextfun ; intro z.
    unfold fldfracgt.
    simpl.
    assert ((weqfldfracgt_f X is is0 is1 is2 nc (nattorig (X := pr1fld (fldfrac X is)) z)) = (weqfldfracgt_f X is is0 is1 is2 nc (tofldfrac X is (nattorig (X := pr1intdom X) z)))).
    { apply maponpaths.
      clear.
      induction z.
      reflexivity.
      rewrite !nattorigS, IHz.
      apply pathsinv0.
      refine (pathscomp0 _ _).
      apply isbinop1funtofldfrac.
      rewrite isunital2funtofldfrac.
      reflexivity. }
    rewrite <- X1.
    reflexivity. }

  assert ( int: forall z', P' z' ) .
  apply setquotunivprop.
  intros x0x1 . destruct x0x1 as [ x0 x1 ] .
  unfold P' .  simpl . unfold weqfldfracgtint_f . simpl.
  destruct ( nc 1%rng 0%rng (nonzeroax X) ) as [ gt0 | lt0 ] . simpl.
  generalize (X0 x0 (pr1 x1) (pr2 x1)).
  apply hinhfun.
  intros (n,Hn).
  exists n.
  apply hinhpr.
  simple refine ( tpair _ _ _ ) .
  simple refine ( tpair _ _ _ ) .  exact ( 1%rng : ( pr1 X ) ) . exact is2 .  simpl .
  repeat (rewrite ( rngrunax2 X _ )) .
  rewrite <- nattorig_natmult in Hn.
  exact Hn.

  destruct ( asy _ _ is2 lt0 ) .

  change ( P x ) .
  rewrite ( e x ) .
  apply int .

Defined.
