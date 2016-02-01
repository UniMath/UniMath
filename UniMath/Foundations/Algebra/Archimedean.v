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
Definition isarchDivisionRig (X : DivRig) (R : hrel X) :=
  ∀ x : X, ∃ n : nat, R (nattorig (X := pr1 X) n) x.
Definition isarchfld (X : fld) (R : hrel X) :=
  ∀ x : X, ∃ n : nat, R (nattorig (X := pr1fld X) n) x.

Theorem isarchrigtorng_gt (X : rig) (R : hrel X) (is : isbinophrel (X := rigaddabmonoid X) R) (is' : isinvbinophrel (X := rigaddabmonoid X) R) (is1 : ∀ x : rigtorng X, ∃ y : X, (¬ R 0%rig y) × coprod (x = setquotpr (eqrelabgrfrac (rigaddabmonoid X)) (y,,0%rig)) (x = setquotpr (eqrelabgrfrac (rigaddabmonoid X)) (0%rig,,y))) ( tra_gt_le : ∀ x y z : X, R x y -> ¬ R z y -> R x z) :
  isarchrig X R -> isarchrig (rigtorng X) (rigtorngrel X is).
Proof.
  intros.
  set (P := λ x y : rigtorng X, ∃ n : nat, rigtorngrel X is (natmult (X := rigaddabmonoid (rigtorng X)) n y) x).
  set (P' := λ x y : abmonoiddirprod (rigaddabmonoid X) (rigaddabmonoid X), ∃ n : nat, rigtorngrel X is (setquotpr (eqrelabgrfrac (rigaddabmonoid X)) (natmult n y)) (setquotpr (eqrelabgrfrac (rigaddabmonoid X)) x)).
  assert ( e : forall x y , P (setquotpr (eqrelabgrfrac (rigaddabmonoid X)) x) (setquotpr (eqrelabgrfrac (rigaddabmonoid X)) y) = P' x y ) .
  { intros xx yy.
    unfold P, P'.
    apply maponpaths.
    apply maponpaths.
    apply funextfun ; intro n.
    apply maponpaths.
    apply map_on_two_paths.
    - induction n.
      + reflexivity.
      + rewrite !natmultS, IHn.
        simple refine (setquotfun2comm _ _ _ _ _ _).
    - reflexivity. }

  intros x y Hy0.
  change (P x y).
  generalize (is1 x) (is1 y).
  apply hinhuniv2.
  intros (x',(Hx,Hx')) (y',(Hy,Hy')).
  destruct Hy' as [Hy' | Hy'].
  assert (Hy'0 : R y' 0%rig).
  { revert Hy0.
    rewrite Hy'.
    apply hinhuniv.
    simpl.
    intros (c,Hc).
    repeat apply (pr2 is') in Hc.
    exact Hc. }
  destruct Hx' as [Hx' | Hx'].
  - rewrite Hx', Hy'.
    rewrite e ; clear e P.
    generalize (X0 x' y' Hy'0).
    apply hinhfun.
    intros n.
    exists (pr1 n).
    unfold rigtorngrel, abgrfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists 0%rig.
    simpl.
    apply (pr2 is).
    assert (∀ n, natmult (X := abmonoiddirprod (rigaddabmonoid X) (rigaddabmonoid X)) n (y',, 0%rig) = (natmult (X := rigaddabmonoid X) n y' ,, 0%rig)).
    { clear.
      induction n.
      - reflexivity.
      - rewrite !natmultS, IHn.
        simpl.
        rewrite riglunax1.
        reflexivity. }
    rewrite X1 ; simpl.
    apply (pr2 is), (pr2 n).
  - rewrite Hx', Hy'.
    rewrite e ; clear e P.
    apply hinhpr.
    exists 1.
    unfold rigtorngrel, abgrfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists 0%rig.
    simpl.
    apply (pr2 is).
    refine (tra_gt_le _ _ _ _ _).
    apply (pr2 is).
    apply Hy'0.
    simpl.
    intro.
    now apply (pr1 is') in X1.
  - apply fromempty, Hy.
    revert Hy0.
    rewrite Hy'.
    apply hinhuniv.
    simpl.
    intros (c,Hc).
    apply (pr2 is'), (pr1 is') in Hc.
    exact Hc.
Defined.

Theorem isarchfldfrac ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1%rng 0%rng ) ( nc : neqchoice R ) ( asy : isasymm R ) : isarchrig X R -> isarchfld (fldfrac X is ) (fldfracgt _  is is0 is1 is2 nc).
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
