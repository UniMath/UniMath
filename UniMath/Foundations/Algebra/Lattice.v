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

Definition pr1lattice : lattice -> setwith2binop := pr1.
Coercion pr1lattice : lattice >-> setwith2binop.
Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max -> lattice :=
  λ (is : islatticeop min max), (X,, min,, max),, is.

Definition lattice2islattice : Π X : lattice, islattice X :=
  λ X : lattice, op1,, op2,, pr2 X.
Definition islattice2lattice : Π X : hSet, islattice X → lattice :=
λ (X : hSet) (is : islattice X), mklattice (pr2 (pr2 is)).

Section lattice_pty.

Context {L : hSet}
        (is : islattice L).

Definition Lmin : binop L := pr1 is.
Definition Lmax : binop L := pr1 (pr2 is).

Lemma isassoc_Lmin :
  isassoc Lmin.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma iscomm_Lmin :
  iscomm Lmin.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma isassoc_Lmax :
  isassoc Lmax.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma iscomm_Lmax :
  iscomm Lmax.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmin_absorb :
  Π x y : L, Lmin x (Lmax x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmax_absorb :
  Π x y : L, Lmax x (Lmin x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.

Lemma Lmin_id :
  Π x : L, Lmin x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin x (Lmax x (Lmin x x)))).
  - rewrite Lmax_absorb.
    reflexivity.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : L, Lmax x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax x (Lmin x (Lmax x x)))).
  - rewrite Lmin_absorb.
    reflexivity.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

(** ** Order in a lattice *)

Section lattice_le.

Context {L : hSet}
        (is : islattice L).

Definition Lle : hrel L :=
  λ (x y : L), hProppair (Lmin is x y = x) ((pr2 L) (Lmin is x y) x).

Lemma isrefl_Lle :
  isrefl Lle.
Proof.
  intros x.
  apply Lmin_id.
Qed.
Lemma isantisymm_Lle :
  isantisymm Lle.
Proof.
  intros x y Hxy Hyx.
  rewrite <- Hxy.
  apply pathscomp0 with (2 := Hyx).
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans Lle.
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.

Lemma Lmin_le_l :
  Π x y : L, Lle (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : L, Lle (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.

Lemma Lmin_ge :
  Π x y z : L, Lle z x → Lle z y → Lle z (Lmin is x y).
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
  Π x y : L, Lle x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_ge_r :
  Π x y : L, Lle y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_ge_l.
Qed.

Lemma Lmax_le :
  isrdistr (Lmax is) (Lmin is)
  → Π x y z : L, Lle x z → Lle y z → Lle (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_eq_l :
  Π x y : L, Lle x y -> Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  Π x y : L, Lle y x -> Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  Π x y : L, Lle y x -> Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  Π x y : L, Lle x y -> Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_le.

Definition islatticewithltrel {X : hSet} (is : islattice X) (lt : StrongOrder X) :=
  (Π x y : X, (¬ (lt x y)) <-> Lle is y x)
    × (Π x y z : X, lt z x -> lt z y -> lt z (Lmin is x y))
    × (Π x y z : X, lt x z -> lt y z -> lt (Lmax is x y) z).

Definition islatticewithlt (X : hSet) :=
  Σ (is : islattice X) (lt : StrongOrder X), islatticewithltrel is lt.

Definition islattice_islatticewithlt {X : hSet} : islatticewithlt X → islattice X :=
  pr1.
Coercion islattice_islatticewithlt : islatticewithlt >-> islattice.

Section latticewithlt.

Context {X : hSet}
        (is : islatticewithlt X).

Definition Llt : StrongOrder X :=
  pr1 (pr2 is).

Lemma notLlt_Lle :
  Π x y : X, (¬ (Llt x y)) <-> Lle is y x.
Proof.
  apply (pr1 (pr2 (pr2 is))).
Qed.
Lemma Llt_Lle :
  Π x y : X, Llt x y -> Lle is x y.
Proof.
  intros x y H.
  apply notLlt_Lle.
  intro H0.
  eapply isirrefl_StrongOrder.
  eapply istrans_StrongOrder.
  exact H.
  exact H0.
Qed.

Lemma istrans_Llt_Lle :
  Π x y z : X, Llt x y → Lle is y z → Llt x z.
Proof.
  intros x y z Hlt Hle.
  generalize (iscotrans_StrongOrder _ _ z _ Hlt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - exact H.
  - apply fromempty.
    refine (pr2 (notLlt_Lle _ _) _ _).
    exact Hle.
    exact H.
Qed.
Lemma istrans_Lle_Llt :
  Π x y z : X, Lle is x y → Llt y z → Llt x z.
Proof.
  intros x y z Hle Hlt.
  generalize (iscotrans_StrongOrder _ _ x _ Hlt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - apply fromempty.
    refine (pr2 (notLlt_Lle _ _) _ _).
    exact Hle.
    exact H.
  - exact H.
Qed.

Lemma Lmin_Llt :
  Π x y z : X, Llt z x -> Llt z y -> Llt z (Lmin is x y).
Proof.
  apply (pr1 (pr2 (pr2 (pr2 is)))).
Qed.
Lemma Lmax_lt  :
  Π x y z : X, Llt x z -> Llt y z -> Llt (Lmax is x y) z.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 is)))).
Qed.

End latticewithlt.
