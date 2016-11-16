(** * Lattice *)

Require Export UniMath.Foundations.Algebra.BinaryOperations.

Unset Automatic Introduction.

(** ** Strong Order *)
(* todo : move it into UniMath.Foundations.Basics.Sets *)

Definition isStrongOrder {X : UU} (R : hrel X) := istrans R × iscotrans R × isirrefl R.
Definition StrongOrder (X : UU) := Σ R : hrel X, isStrongOrder R.
Definition pairStrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  tpair (fun R : hrel X => isStrongOrder R ) R is.
Definition pr1StrongOrder {X : UU} : StrongOrder X → hrel X := pr1.
Coercion  pr1StrongOrder : StrongOrder >-> hrel.

Section so_pty.

Context {X : UU}.
Context (R : StrongOrder X).

Definition istrans_StrongOrder : istrans R :=
  pr1 (pr2 R).
Definition iscotrans_StrongOrder : iscotrans R :=
  pr1 (pr2 (pr2 R)).
Definition isirrefl_StrongOrder : isirrefl R :=
  pr2 (pr2 (pr2 R)).

End so_pty.

Definition isStrongOrder_quotrel {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros X R L is H.
  repeat split.
  - apply istransquotrel, (pr1 H).
  - apply iscotransquotrel, (pr1 (pr2 H)).
  - apply isirreflquotrel, (pr2 (pr2 H)).
Defined.

(** ** Definition *)

Definition islatticeop {X : hSet} (min max : binop X) :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (Π x y : X, min x (max x y) = x)
    × (Π x y : X, max x (min x y) = x).
Definition islattice (X : hSet) := Σ min max : binop X, islatticeop min max.
Definition lattice := Σ X : setwith2binop, islatticeop (X := X) op1 op2.

Definition pr1lattice : lattice → setwith2binop := pr1.
Coercion pr1lattice : lattice >-> setwith2binop.
Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max → lattice :=
  λ (is : islatticeop min max), (X,, min,, max),, is.

Definition lattice2islattice : Π X : lattice, islattice X :=
  λ X : lattice, op1,, op2,, pr2 X.
Definition islattice2lattice : Π X : hSet, islattice X → lattice :=
λ (X : hSet) (is : islattice X), mklattice (pr2 (pr2 is)).

Definition Lmin {X : hSet} (is : islattice X) : binop X := pr1 is.
Definition Lmax {X : hSet} (is : islattice X) : binop X := pr1 (pr2 is).

Section lattice_pty.

Context {X : hSet}
        (is : islattice X).

Lemma isassoc_Lmin :
  isassoc (Lmin is).
Proof.
  exact (pr1 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma iscomm_Lmin :
  iscomm (Lmin is).
Proof.
  exact (pr2 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma isassoc_Lmax :
  isassoc (Lmax is).
Proof.
  exact (pr1 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma iscomm_Lmax :
  iscomm (Lmax is).
Proof.
  exact (pr2 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmin_absorb :
  Π x y : X, Lmin is x (Lmax is x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmax_absorb :
  Π x y : X, Lmax is x (Lmin is x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.

Lemma Lmin_id :
  Π x : X, Lmin is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin is x (Lmax is x (Lmin is x x)))).
  - apply maponpaths, pathsinv0, Lmax_absorb.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : X, Lmax is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax is x (Lmin is x (Lmax is x x)))).
  - apply maponpaths, pathsinv0, Lmin_absorb.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

(** ** Order in a lattice *)

(** [Lle] *)

Definition Lle {X : hSet} (is : islattice X) : hrel X :=
  λ (x y : X), hProppair (Lmin is x y = x) ((pr2 X) (Lmin is x y) x).

Section lattice_le.

Context {X : hSet}
        (is : islattice X).

Lemma isrefl_Lle :
  isrefl (Lle is).
Proof.
  intros x.
  apply Lmin_id.
Qed.
Lemma isantisymm_Lle :
  isantisymm (Lle is).
Proof.
  intros x y Hxy Hyx.
  rewrite <- Hxy.
  apply pathscomp0 with (2 := Hyx).
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans (Lle is).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.

Lemma Lmin_le_l :
  Π x y : X, Lle is (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : X, Lle is (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.

Lemma Lmin_ge :
  Π x y z : X, Lle is z x → Lle is z y → Lle is z (Lmin is x y).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite (iscomm_Lmin _ x), <- isassoc_Lmin.
  rewrite (isassoc_Lmin _ _ _ y), Lmin_id.
  rewrite isassoc_Lmin, (iscomm_Lmin _ y).
  rewrite isassoc_Lmin, <- (isassoc_Lmin _ x), Lmin_id.
  apply pathsinv0, isassoc_Lmin.
Qed.

Lemma Lmax_ge_l :
  Π x y : X, Lle is x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_ge_r :
  Π x y : X, Lle is y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_ge_l.
Qed.

Lemma Lmax_le :
  isrdistr (Lmax is) (Lmin is)
  → Π x y z : X, (Lle is) x z → (Lle is) y z → (Lle is) (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_eq_l :
  Π x y : X, Lle is x y → Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  Π x y : X, Lle is y x → Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  Π x y : X, Lle is y x → Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  Π x y : X, Lle is x y → Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_le.

(** [Lge] *)

Definition Lge {X : hSet} (is : islattice X) : hrel X :=
  λ x y : X, Lle is y x.

(** ** Lattice with a strong order *)

Definition islatticewithgtrel {X : hSet} (is : islattice X) (gt : StrongOrder X) :=
  (Π x y : X, (¬ (gt x y)) <-> Lle is x y)
    × (Π x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
    × (Π x y z : X, gt z x → gt z y → gt z (Lmax is x y)).

Definition islatticewithgt (X : hSet) :=
  Σ (is : islattice X) (gt : StrongOrder X), islatticewithgtrel is gt.

Definition islattice_islatticewithgt {X : hSet} : islatticewithgt X → islattice X :=
  pr1.
Coercion islattice_islatticewithgt : islatticewithgt >-> islattice.

(** [Lgt] *)

Definition Lgt {X : hSet} (is : islatticewithgt X) : StrongOrder X :=
  pr1 (pr2 is).

Section latticewithgt_def.

Context {X : hSet}
        (is : islatticewithgt X).

Lemma notLgt_Lle :
  Π x y : X, (¬ (Lgt is x y)) <-> Lle is x y.
Proof.
  apply (pr1 (pr2 (pr2 is))).
Qed.

Definition isirrefl_Lgt : isirrefl (Lgt is) :=
  isirrefl_StrongOrder (Lgt is).
Definition istrans_Lgt : istrans (Lgt is) :=
  istrans_StrongOrder (Lgt is).
Definition iscotrans_Lgt : iscotrans (Lgt is) :=
  iscotrans_StrongOrder (Lgt is).

Lemma Lmin_Lgt :
  Π x y z : X, Lgt is x z → Lgt is y z → Lgt is (Lmin is x y) z.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 is)))).
Qed.

Lemma Lmax_gt  :
  Π x y z : X, Lgt is z x → Lgt is z y → Lgt is z (Lmax is x y).
Proof.
  apply (pr2 (pr2 (pr2 (pr2 is)))).
Qed.

End latticewithgt_def.

Section latticewithgt_pty.

Context {X : hSet}
        (is : islatticewithgt X).

Lemma Lgt_Lge :
  Π x y : X, Lgt is x y → Lge is x y.
Proof.
  intros x y H.
  apply notLgt_Lle.
  intro H0.
  eapply isirrefl_Lgt.
  eapply istrans_Lgt.
  exact H.
  exact H0.
Qed.

Lemma istrans_Lgt_Lge :
  Π x y z : X, Lgt is x y → Lge is y z → Lgt is x z.
Proof.
  intros x y z Hgt Hge.
  generalize (iscotrans_Lgt _ _ z _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - exact H.
  - apply fromempty.
    refine (pr2 (notLgt_Lle _ _ _) _ _).
    exact Hge.
    exact H.
Qed.
Lemma istrans_Lge_Lgt :
  Π x y z : X, Lge is x y → Lgt is y z → Lgt is x z.
Proof.
  intros x y z Hge Hgt.
  generalize (iscotrans_Lgt _ _ x _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - apply fromempty.
    refine (pr2 (notLgt_Lle _ _ _) _ _).
    exact Hge.
    exact H.
  - exact H.
Qed.

End latticewithgt_pty.
