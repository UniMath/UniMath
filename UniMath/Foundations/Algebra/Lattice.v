(** * Lattice *)

Require Export UniMath.Foundations.Algebra.BinaryOperations.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.

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
  pattern x at 2 ; rewrite <- (Lmax_absorb x x).
  apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : L, Lmax x x = x.
Proof.
  intros x.
  pattern x at 2 ; rewrite <- (Lmin_absorb x x).
  apply Lmax_absorb.
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
  pattern y at 2 ; rewrite <- Hyx.
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

Section tminus_pty.

Context {X : abmonoid}
        (is : islattice X)
        (minus : binop X)
        (is0 : istminus is minus)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmin is) (Lmax is))
        (is5 : isrdistr (Lmax is) (Lmin is)).

Lemma tminus_0_r :
  Π x : X, minus x 0 = Lmax is x 0.
Proof.
  intros x.
  rewrite <- (runax _ (minus _ _)).
  apply is0.
Qed.

Lemma tminus_eq_0 :
  Π x y : X, Lle is x y → minus x y = 0.
Proof.
  intros x y H.
  apply (is1 y).
  rewrite is0, lunax.
  apply Lmax_eq_r, H.
Qed.

Lemma tminus_0_l_ge0 :
  Π x : X, Lle is 0 x → minus 0 x = 0.
Proof.
  intros x Hx.
  apply tminus_eq_0, Hx.
Qed.
Lemma tminus_0_l_le0 :
  Π x : X, Lle is x 0 → minus 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite is0.
  apply Lmax_eq_l, Hx.
Qed.

Lemma tminus_ge_0 :
  Π x y : X, Lle is 0 (minus x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite is0, lunax.
  apply Lmax_ge_r.
Qed.

Lemma tminus_le :
  Π x y : X,
          Lle is 0 x → Lle is 0 y
          → Lle is (minus x y) x.
Proof.
  intros x y Hx Hy.
  apply (op_le_r' _ is1 is3 y).
  rewrite is0.
  apply Lmax_le.
  apply is5.
  pattern x at 1 ; rewrite <- (lunax _ x), (commax _ x).
  now apply op_le_r.
  pattern y at 1 ; rewrite <- (lunax _ y).
  now apply op_le_r.
Qed.

Lemma tminus_le_r :
  Π k x y : X, Lle is x y → Lle is (minus x k) (minus y k).
Proof.
  intros k x y <-.
  apply (is1 k).
  rewrite is3, !is0.
  rewrite is4, isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.

Lemma tminus_Lmax_l :
  Π k x y : X, minus (Lmax is x y) k = Lmax is (minus x k) (minus y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is2, !is0.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma tminus_Lmin_l :
  Π k x y : X, minus (Lmin is x y) k = Lmin is (minus x k) (minus y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is3, !is0.
  apply is4.
Qed.

Lemma tminus_le_l :
  Π k x y : X, Lle is y x → Lle is (minus k x) (minus k y).
Proof.
  intros k x y H.
  apply (is1 y).
  rewrite is3, is0.
  apply (is1 x).
  rewrite is3, assocax, (commax _ y), <- assocax, is0.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

End tminus_pty.

(** *** Truncated minus and abgrfrac *)

Section abgrfrac_minus.

Context {X : abmonoid}
        (is : islattice X)
        (minus : binop X)
        (is0 : istminus is minus)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmax is) (Lmin is)).

Lemma iscomprel_tminus :
    iscomprelfun (eqrelabgrfrac X) (λ x, minus (pr1 x) (pr2 x)).
Proof.
  intros x y.
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 X))).
  intros c.
  apply (is1 (pr2 x + pr2 y + pr1 c)).
  rewrite <- 2!assocax, is0.
  rewrite (commax _ (pr2 x)), <- 2!assocax, is0.
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
  abgrfracelt (setquotpr _ c) = (minus (pr1 c) (pr2 c) ,, minus (pr2 c) (pr1 c)).
Proof.
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
  generalize (pr1 (pr2 x)).
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 (abgrfrac X)))).
  intros c ; simpl.
  rewrite <- (setquotl0 (eqrelabgrfrac X) x c).
  refine (iscompsetquotpr (eqrelabgrfrac X) _ _ _).
  rewrite abgrfracelt_simpl.
  apply hinhpr.
  exists 0 ; simpl.
  rewrite (commax _ (pr1 (pr1 c))), !is0.
  now rewrite iscomm_Lmax.
Qed.

Lemma abgrfracelt_correct' (x : abgrfrac X) :
  abgrfracelt (setquotpr _ (abgrfracelt x)) = abgrfracelt x.
Proof.
  now rewrite abgrfracelt_correct.
Qed.

End abgrfrac_minus.

(** ** lattice in abgrfrac *)

Lemma abgrfrac_setquotpr_equiv {X : abmonoid} :
  Π k x y : X,
  setquotpr (eqrelabgrfrac X) (x,,y) = setquotpr (eqrelabgrfrac X) (x + k,,y + k).
Proof.
  intros k x y.
  apply iscompsetquotpr, hinhpr.
  exists 0 ; simpl.
  rewrite !(assocax X), !runax, (commax X y).
  reflexivity.
Qed.

Section lattice_abgrfrac.

Context {X : abmonoid}
        {min max : binop X}
        (is : islatticeop min max)
        (minus : binop X)
        (is0 : istminus (_,,_,,is) minus)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr max op)
        (is3 : isrdistr min op)
        (is4 : isrdistr max min)
        (is5 : isrdistr min max).

Definition abgrfrac_min : binop (abgrfrac X).
Proof.
  intros x y.
  apply setquotpr.
  split.
  - apply min.
    apply (pr1 (abgrfracelt (_,,_,,is) minus is0 is1 is2 x)).
    apply (pr1 (abgrfracelt (_,,_,,is) minus is0 is1 is2 y)).
  - apply max.
    apply (pr2 (abgrfracelt (_,,_,,is) minus is0 is1 is2 x)).
    apply (pr2 (abgrfracelt (_,,_,,is) minus is0 is1 is2 y)).
Defined.

Definition abgrfrac_max : binop (abgrfrac X).
Proof.
  intros x y.
  apply setquotpr.
  split.
  - apply max.
    apply (pr1 (abgrfracelt (_,,_,,is) minus is0 is1 is2 x)).
    apply (pr1 (abgrfracelt (_,,_,,is) minus is0 is1 is2 y)).
  - apply min.
    apply (pr2 (abgrfracelt (_,,_,,is) minus is0 is1 is2 x)).
    apply (pr2 (abgrfracelt (_,,_,,is) minus is0 is1 is2 y)).
Defined.

Lemma iscomm_abgrfrac_min :
  iscomm abgrfrac_min.
Proof.
  intros x y.
  unfold abgrfrac_min.
  set (x' := abgrfracelt (min,, max,, is) minus is0 is1 is2 x).
  set (y' := abgrfracelt (min,, max,, is) minus is0 is1 is2 y).
  rewrite (iscomm_Lmin (_,,_,,is)), (iscomm_Lmax (_,,_,,is)).
  reflexivity.
Qed.

Lemma isassoc_abgrfrac_min :
  isassoc abgrfrac_min.
Admitted.

Lemma iscomm_abgrfrac_max :
  iscomm abgrfrac_max.
Proof.
  intros x y.
  unfold abgrfrac_max.
  set (x' := abgrfracelt (min,, max,, is) minus is0 is1 is2 x).
  set (y' := abgrfracelt (min,, max,, is) minus is0 is1 is2 y).
  rewrite (iscomm_Lmin (_,,_,,is)), (iscomm_Lmax (_,,_,,is)).
  reflexivity.
Qed.

Lemma isassoc_abgrfrac_max :
  isassoc abgrfrac_max.
Admitted.

Lemma isabsorb_abgrfrac_max_min :
  Π x y : abgrfrac X, abgrfrac_max x (abgrfrac_min x y) = x.
Proof.
  intros x y.
  unfold abgrfrac_max, abgrfrac_min.
  set (x' := abgrfracelt (min,, max,, is) minus is0 is1 is2 x).
  set (y' := abgrfracelt (min,, max,, is) minus is0 is1 is2 y).

  generalize (abgrfracelt_correct' (min,, max,, is) minus is0 is1 is2 x).
  fold x'.
  rewrite abgrfracelt_simpl.
  intros Hx'.

  generalize (abgrfracelt_correct' (min,, max,, is) minus is0 is1 is2 y).
  fold y'.
  rewrite abgrfracelt_simpl.
  intros Hy'.

  rewrite !(abgrfracelt_simpl (min,, max,, is)),
          !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite (Lmax_eq_l (min,, max,, is)), (Lmin_eq_l (min,, max,, is)).

  - rewrite <- tppr.
    apply abgrfracelt_correct.

  - pattern x' at 1 ; rewrite <- Hx', rewrite_pr2_tpair.
    refine (istrans_Lle _ _ _ _ _ _).
    + apply tminus_le_r.
      exact is0.
      exact is1.
      exact is3.
      exact is5.
      apply (Lmax_ge_l (min,,max,,is)).
    + apply tminus_le_l.
      exact is0.
      exact is1.
      exact is2.
      exact is3.
      exact is5.
      apply (Lmin_le_l (min,,max,,is)).
  - refine (istrans_Lle _ _ _ _ _ _).
    + apply tminus_le.
      exact is0.
      exact is1.
      exact is3.
      exact is4.
      apply Lmin_ge.
      rewrite <- Hx', rewrite_pr1_tpair.
      now apply tminus_ge_0.
      rewrite <- Hy', rewrite_pr1_tpair.
      now apply tminus_ge_0.
      refine (istrans_Lle _ _ _ _ _ _).
      2: apply (Lmax_ge_l (_,,_,,is)).
      rewrite <- Hx', rewrite_pr2_tpair.
      now apply tminus_ge_0.
    + apply Lmin_le_l.
Qed.

Lemma isabsorb_abgrfrac_min_max :
  Π x y : abgrfrac X, abgrfrac_min x (abgrfrac_max x y) = x.
Admitted.

End lattice_abgrfrac.