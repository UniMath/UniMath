(** * Lattice *)

Require Export UniMath.Foundations.Algebra.BinaryOperations.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.

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

(** ** Lattice with a total order *)

Section lattice_deceq.

Context {L : hSet}
        (is : islattice L)
        (dec : Π x y : L, (Lle is x y) ⨿ (Lle is y x)).

Lemma Lmin_case_strong :
  Π (P : L → UU) (x y : L),
  (Lle is x y → P x) → (Lle is y x → P y) → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  induction (dec x y) as [H | H].
  - rewrite H.
    apply Hx, H.
  - rewrite iscomm_Lmin, H.
    apply Hy, H.
Qed.
Lemma Lmin_case :
  Π (P : L → UU) (x y : L),
  P x → P y → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  Π (P : L → UU) (x y : L),
  (Lle is y x → P x) → (Lle is x y → P y) → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  induction (dec x y) as [H | H].
  - rewrite Lmax_eq_r.
    apply Hy, H.
    exact H.
  - rewrite Lmax_eq_l.
    apply Hx, H.
    exact H.
Qed.
Lemma Lmax_case :
  Π (P : L → UU) (x y : L),
  P x → P y → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

End lattice_deceq.

(** *** Lattice in an abmonoid *)

Local Open Scope addmonoid.

Section lattice_abmonoid.

Context {X : abmonoid}
        (is : islattice X)
        (is0 : Π x y z : X, y + x = z + x → y = z)
        (is1 : isrdistr (Lmax is) op)
        (is2 : isrdistr (Lmin is) op)
        (is3 : isrdistr (Lmin is) (Lmax is)).

Lemma op_le_r :
  Π k x y : X, Lle is x y → Lle is (x + k) (y + k).
Proof.
  intros k x y H.
  unfold Lle ; simpl.
  now rewrite <- is2, H.
Qed.
Lemma op_le_r' :
  Π k x y : X, Lle is (x + k) (y + k) → Lle is x y.
Proof.
  intros k x y H.
  apply (is0 k).
  now rewrite is2, H.
Qed.

End lattice_abmonoid.

(** ** Truncated minus *)

Definition istminus {X : abmonoid} (is : islattice X) (minus : binop X) :=
  Π x y : X, minus x y + y = Lmax is x y.

Definition extminus {X : abmonoid} (is : islattice X) :=
  Σ minus : binop X, istminus is minus.

Definition tminus {X : abmonoid} {is : islattice X} (ex : extminus is) : binop X :=
  pr1 ex.

Lemma istminus_ex {X : abmonoid} {is : islattice X} (ex : extminus is) :
  Π x y : X, tminus ex x y + y = Lmax is x y.
Proof.
  intros X is ex.
  apply (pr2 ex).
Qed.

Section tminus_pty.

Context {X : abmonoid}
        {is : islattice X}
        (ex : extminus is)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmin is) (Lmax is))
        (is5 : isrdistr (Lmax is) (Lmin is)).

Lemma tminus_0_r :
  Π x : X, tminus ex x 0 = Lmax is x 0.
Proof.
  intros x.
  rewrite <- (runax _ (tminus _ _ _)).
  apply (istminus_ex).
Qed.

Lemma tminus_eq_0 :
  Π x y : X, Lle is x y → tminus ex x y = 0.
Proof.
  intros x y H.
  apply (is1 y).
  rewrite istminus_ex, lunax.
  apply Lmax_eq_r, H.
Qed.

Lemma tminus_0_l_ge0 :
  Π x : X, Lle is 0 x → tminus ex 0 x = 0.
Proof.
  intros x Hx.
  apply tminus_eq_0, Hx.
Qed.
Lemma tminus_0_l_le0 :
  Π x : X, Lle is x 0 → tminus ex 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite istminus_ex.
  apply Lmax_eq_l, Hx.
Qed.

Lemma tminus_ge_0 :
  Π x y : X, Lle is 0 (tminus ex x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite istminus_ex, lunax.
  apply Lmax_ge_r.
Qed.

Lemma tminus_le :
  Π x y : X,
          Lle is 0 x → Lle is 0 y
          → Lle is (tminus ex x y) x.
Proof.
  intros x y Hx Hy.
  apply (op_le_r' _ is1 is3 y).
  rewrite istminus_ex.
  apply Lmax_le.
  - apply is5.
  - apply istrans_Lle with (0 + x).
    + rewrite (lunax _ x).
      apply isrefl_Lle.
    + rewrite (commax _ x).
      now apply op_le_r.
  - apply istrans_Lle with (0 + y).
    + rewrite (lunax _ y).
      apply isrefl_Lle.
    + now apply op_le_r.
Qed.

Lemma tminus_tminus :
  Π x y, Lle is 0 x → Lle is x y → tminus ex y (tminus ex y x) = x.
Proof.
  intros x y Hx Hxy.
  apply (is1 (tminus ex y x)).
  rewrite (commax _ x), !istminus_ex.
  rewrite !Lmax_eq_l.
  - reflexivity.
  - exact Hxy.
  - apply tminus_le.
    apply istrans_Lle with x.
    exact Hx.
    exact Hxy.
    exact Hx.
Qed.

Lemma tminus_le_r :
  Π k x y : X, Lle is x y → Lle is (tminus ex x k) (tminus ex y k).
Proof.
  intros k x y <-.
  apply (is1 k).
  rewrite is3, !istminus_ex.
  rewrite is4, isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma tminus_le_l :
  Π k x y : X, Lle is y x → Lle is (tminus ex k x) (tminus ex k y).
Proof.
  intros k x y H.
  apply (is1 y).
  rewrite is3, istminus_ex.
  apply (is1 x).
  rewrite is3, assocax, (commax _ y), <- assocax, istminus_ex.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

Lemma tminus_Lmax_l :
  Π (k x y : X),
  tminus ex (Lmax is x y) k = Lmax is (tminus ex x k) (tminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is2, !istminus_ex.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma tminus_Lmax_r :
  Π (k x y : X),
  Lle is (Lmin is (y + y) (x + x)) (x + y) →
  tminus ex k (Lmax is x y) = Lmin is (tminus ex k x) (tminus ex k y).
Proof.
  intros k x y H.
  apply (is1 (Lmax is x y)).
  rewrite is3, istminus_ex.
  rewrite !(commax _ _ (Lmax _ _ _)), !is2.
  rewrite !(commax _ _ (tminus _ _ _)), !istminus_ex.
  rewrite (iscomm_Lmax _ (_*_)%multmonoid (Lmax _ _ _)).
  rewrite !isassoc_Lmax, !(iscomm_Lmax _ k).
  rewrite <- is4.

  apply (is1 x).
  rewrite !is2, is3, !is2.
  rewrite assocax, (commax _ y x), <- assocax.
  rewrite istminus_ex, is2.

  apply (is1 y).
  rewrite !is2, is3, !is2.
  rewrite !assocax, (commax _ (tminus _ _ _)), !assocax, (commax _ _ (tminus _ _ _)).
  rewrite istminus_ex.
  rewrite (commax _ _ (Lmax _ _ _)), is2.
  rewrite (commax _ _ (Lmax _ _ _)), is2.

  rewrite 4!(commax _ _ x).
  rewrite <- (isassoc_Lmax _ _ _ (x * (y * y))%multmonoid).
  rewrite (iscomm_Lmax _ (x * (y * y))%multmonoid (Lmax _ _ _)).

  rewrite <- is4.
  rewrite (iscomm_Lmax _ (x * (x * y))%multmonoid (k * (y * y))%multmonoid), <- is4.
  rewrite !(commax _ k), <- !assocax.
  rewrite <- is3.
  rewrite !(iscomm_Lmax _ _ (x * y * k)%multmonoid), <- !isassoc_Lmax.
  rewrite (Lmax_eq_l _ (x * y * k)%multmonoid
                     (Lmin is (y * y) (x * x) * k)%multmonoid).
  reflexivity.
  apply op_le_r.
  exact is3.
  exact H.
Qed.

Lemma tminus_Lmin_l :
  Π k x y : X, tminus ex (Lmin is x y) k = Lmin is (tminus ex x k) (tminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is3, !istminus_ex.
  apply is4.
Qed.

End tminus_pty.

Lemma abgr_tminus {X : abgr} (is : islattice X) :
  isrdistr (Lmax is) op →
  istminus (X := abgrtoabmonoid X) is (λ x y : X, Lmax is 0 (x + grinv X y)).
Proof.
  intros X is H x y.
  rewrite H, assocax, grlinvax, lunax, runax.
  apply iscomm_Lmax.
Qed.

Definition extminuswithlt {X : abmonoid} (is : islatticewithlt X) :=
  Σ (ex : extminus is), Π x y : X, Llt is 0 (tminus ex y x) → Llt is x y.
Definition extminuswithlt_extminus {X : abmonoid} (is : islatticewithlt X) :
  extminuswithlt is → extminus is := pr1.
Coercion extminuswithlt_extminus : extminuswithlt >-> extminus.

Section tminus_lt.

Context {X : abmonoid}
        (is : islatticewithlt X)
        (ex : extminuswithlt is)
        (is0 : Π x y z : X, Llt is y z → Llt is (y + x) (z + x))
        (is1 : Π x y z : X, Llt is (y + x) (z + x) → Llt is y z).

Lemma tminus_pos :
  Π x y : X, Llt is x y → Llt is 0 (tminus ex y x).
Proof.
  intros x y.
  intros H.
  apply (is1 x).
  rewrite lunax, istminus_ex.
  rewrite Lmax_eq_l.
  exact H.
  apply Llt_Lle, H.
Qed.

Lemma tminus_pos' :
  Π x y : X, Llt is 0 (tminus ex y x) → Llt is x y.
Proof.
  exact (pr2 ex).
Qed.

End tminus_lt.

(** *** Truncated minus and abgrfrac *)

Section abgrfrac_minus.

Context {X : abmonoid}
        {is : islattice X}
        (ex : extminus is)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmax is) (Lmin is)).

Lemma iscomprel_tminus :
    iscomprelfun (eqrelabgrfrac X) (λ x, tminus ex (pr1 x) (pr2 x)).
Proof.
  intros x y.
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 X))).
  intros c.
  apply (is1 (pr2 x + pr2 y + pr1 c)).
  rewrite <- 2!assocax, istminus_ex.
  rewrite (commax _ (pr2 x)), <- 2!assocax, istminus_ex.
  rewrite !is2, (pr2 c), (commax _ (pr2 x)).
  reflexivity.
Qed.

Definition abgrfracelt (x : abgrfrac X) : X × X.
Proof.
  split.
  - refine (setquotuniv _ _ _ _ _).
    apply iscomprel_tminus.
    apply x.
  - refine (setquotuniv _ _ _ _ _).
    apply iscomprel_tminus.
    apply (grinv (abgrfrac X) x).
Defined.

Lemma abgrfracelt_simpl (c : X × X) :
  abgrfracelt (setquotpr _ c) = tminus ex (pr1 c) (pr2 c) ,, tminus ex (pr2 c) (pr1 c).
Proof.
  intros c.
  unfold abgrfracelt.
  unfold grinv ; simpl.
  unfold abgrfracinv ; simpl.
  rewrite (setquotfuncomm (eqrelabgrfrac X) (eqrelabgrfrac X)).
  rewrite !(setquotunivcomm (eqrelabgrfrac X)).
  reflexivity.
Qed.

Lemma abgrfracelt_correct (x : abgrfrac X) :
  setquotpr _ (abgrfracelt x) = x.
Proof.
  intros x.
  generalize (pr1 (pr2 x)).
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 (abgrfrac X)))).
  intros c ; simpl.
  rewrite <- (setquotl0 (eqrelabgrfrac X) x c).
  refine (iscompsetquotpr (eqrelabgrfrac X) _ _ _).
  rewrite abgrfracelt_simpl.
  apply hinhpr.
  exists 0 ; simpl.
  rewrite (commax _ (pr1 (pr1 c))), !(istminus_ex ex).
  now rewrite iscomm_Lmax.
Qed.

Lemma abgrfracelt_correct' (x : abgrfrac X) :
  abgrfracelt (setquotpr _ (abgrfracelt x)) = abgrfracelt x.
Proof.
  intros x.
  now rewrite abgrfracelt_correct.
Qed.

End abgrfrac_minus.
