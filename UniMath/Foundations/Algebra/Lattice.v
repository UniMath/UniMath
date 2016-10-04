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

Context {L : lattice}.

Definition Lmin : binop L := op1.
Definition Lmax : binop L := op2.
Definition Lle : hrel L :=
  λ (x y : L), hProppair (Lmin x y = x) (pr2 (pr1 (pr1 L)) (Lmin x y) x).

Lemma isassoc_Lmin :
  isassoc Lmin.
Proof.
  exact (pr1 (pr1 (pr2 L))).
Qed.
Lemma iscomm_Lmin :
  iscomm Lmin.
Proof.
  exact (pr2 (pr1 (pr2 L))).
Qed.
Lemma isassoc_Lmax :
  isassoc Lmax.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 L)))).
Qed.
Lemma iscomm_Lmax :
  iscomm Lmax.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 L)))).
Qed.
Lemma Lmin_absorb :
  Π x y : L, Lmin x (Lmax x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 L)))).
Qed.
Lemma Lmax_absorb :
  Π x y : L, Lmax x (Lmin x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 L)))).
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
  Π x y : L, Lle (Lmin x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : L, Lle (Lmin x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmax_le_l :
  Π x y : L, Lle x (Lmax x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  Π x y : L, Lle y (Lmax x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.

Lemma Lmin_eq_l :
  Π x y : L, Lle x y -> Lmin x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  Π x y : L, Lle y x -> Lmin x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  Π x y : L, Lle y x -> Lmax x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  Π x y : L, Lle x y -> Lmax x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_pty.

(** ** Troncated minus *)

Local Open Scope addmonoid.

Definition istminus {X : abmonoid} (is : islattice X) (minus : binop X) :=
  Π x y : X, minus x y + y = Lmax (L := islattice2lattice X is) x y.

Definition extminus {X : abmonoid} (is : islattice X) :=
  Σ minus : binop X, istminus is minus.

(** *** Troncated minus and abgrfrac *)

Lemma iscomprel_tminus {X : abmonoid} (is : islattice X) (minus : binop X) :
  istminus is minus
  → (Π x y z : X, y + x = z + x → y = z)
  → isrdistr (Lmax (L := islattice2lattice X is)) op
  → iscomprelfun (eqrelabgrfrac X) (λ x, minus (pr1 x) (pr2 x)).
Proof.
  intros Hminus H H0.
  intros x y.
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 X))).
  intros c.
  apply (H (pr2 x + pr2 y + pr1 c)).
  rewrite <- 2!assocax, Hminus.
  rewrite (commax _ (pr2 x)), <- 2!assocax, Hminus.
  rewrite !H0, (pr2 c), (commax _ (pr2 x)).
  reflexivity.
Qed.

Definition abgrfracelt {X : abmonoid} (is : islattice X) (minus : binop X)
           (is0 : istminus is minus)
           (is1 : Π x y z : X, y + x = z + x → y = z)
           (is2 : isrdistr (Lmax (L := islattice2lattice X is)) op)
           (x : abgrfrac X) : X × X.
Proof.
  split.
  - refine (setquotuniv _ _ _ _ _).
    apply (iscomprel_tminus is _ is0 is1 is2).
    apply x.
  - refine (setquotuniv _ _ _ _ _).
    apply (iscomprel_tminus is _ is0 is1 is2).
    apply (grinv (abgrfrac X) x).
Defined.

Lemma abgrfracelt_correct {X : abmonoid} (is : islattice X) (minus : binop X)
           (is0 : istminus is minus)
           (is1 : Π x y z : X, y + x = z + x → y = z)
           (is2 : isrdistr (Lmax (L := islattice2lattice X is)) op)
           (x : abgrfrac X) :
  setquotpr _ (abgrfracelt is minus is0 is1 is2 x) = x.
Proof.
  generalize (pr1 (pr2 x)).
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 (abgrfrac X)))).
  intros c ; simpl.
  rewrite <- (setquotl0 (eqrelabgrfrac X) x c).
  refine (iscompsetquotpr (eqrelabgrfrac X) _ _ _).
  apply hinhpr.
  exists 0 ; simpl.
  unfold grinv ; simpl.
  unfold abgrfracinv ; simpl.
  rewrite (setquotfuncomm (eqrelabgrfrac X) _), !(setquotunivcomm (eqrelabgrfrac X) (pr1 X)) ; simpl.
  rewrite (commax _ (pr1 (pr1 c))), !is0.
  now rewrite iscomm_Lmax.
Qed.
