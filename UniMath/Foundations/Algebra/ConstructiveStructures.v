(** * Definition of appartness relationConstructive Algebraic Structures *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Foundations.Algebra.DivisionRig.
Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

Local Open Scope constructive_logic.
Local Open Scope rig_scope.
Local Open Scope rng_scope.

(** ** Constructive rig *)


Definition ConstructiveRig :=
  Σ X : apsetwith2binop, @isrigops X op1 op2.
Definition ConstructiveRig_set (X : ConstructiveRig) : apsetwith2binop := pr1 X.
Definition ConstructiveRig_rig : ConstructiveRig -> rig :=
  λ X : ConstructiveRig, (apsetwith2binop_setwith2binop (ConstructiveRig_set X)),, pr2 X.
Coercion ConstructiveRig_rig : ConstructiveRig >-> rig.

Definition isnonzeroCR (X : ConstructiveRig) := (1%rig : X) # (0%rig : X).

(** Lemmas *)

Section CRig_pty.

Context {X : ConstructiveRig}.

Lemma apCRigplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCRigmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CRigzero_CRigplus :
  forall x : X, 0%rig + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CRigzero_CRigplus :
  forall x : X, x + 0%rig = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CRigplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CRigplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CRigone_CRigmult :
  forall x : X, 1%rig * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CRigone_CRigmult :
  forall x : X, x * 1%rig = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CRigmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma islabsorb_CRigzero_CRigmult :
  ∀ x : X, 0%rig * x = 0%rig.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CRigzero_CRigmult :
  ∀ x : X, x * 0%rig = 0%rig.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CRigplus_CRigmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Lemma CRigmultapCRigzero :
  forall x y : X, x * y # (0%rig : X) -> x # (0%rig : X) ∧ y # (0%rig : X).
Proof.
  intros x y Hmult.
  split.
  - apply islapbinop_op2 with y.
    now rewrite islabsorb_CRigzero_CRigmult.
  - apply israpbinop_op2 with x.
    now rewrite israbsorb_CRigzero_CRigmult.
Qed.

End CRig_pty.

(** ** Constructive commutative rig *)

Definition ConstructiveCommutativeRig :=
  Σ X : apsetwith2binop, @iscommrigops X op1 op2.
Definition ConstructiveCommutativeRig_CommutativeRig (X : ConstructiveCommutativeRig) : ConstructiveRig :=
  pr1 X,, pr1 (pr2 X).
Coercion ConstructiveCommutativeRig_CommutativeRig : ConstructiveCommutativeRig >-> ConstructiveRig.
Definition ConstructiveCommutativeRig_commrig : ConstructiveCommutativeRig -> commrig :=
  λ X : ConstructiveCommutativeRig, (apsetwith2binop_setwith2binop (ConstructiveRig_set X)),, pr2 X.

(** Lemmas *)

Section CCRig_pty.

Context {X : ConstructiveCommutativeRig}.

Lemma apCCRigplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCCRigmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CCRigzero_CCRigplus :
  forall x : X, 0%rig + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CCRigzero_CCRigplus :
  forall x : X, x + 0%rig = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CCRigplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CCRigplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CCRigone_CCRigmult :
  forall x : X, 1%rig * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CCRigone_CCRigmult :
  forall x : X, x * 1%rig = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CCRigmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma iscomm_CCRigmult :
  forall x y : X, x * y = y * x.
Proof.
  now apply (rigcomm2 (ConstructiveCommutativeRig_commrig X)).
Qed.
Lemma islabsorb_CCRigzero_CCRigmult :
  ∀ x : X, 0%rig * x = 0%rig.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CCRigzero_CCRigmult :
  ∀ x : X, x * 0%rig = 0%rig.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CCRigplus_CCRigmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

End CCRig_pty.

(** ** Constructive ring *)

Definition ConstructiveRing := Σ X : apsetwith2binop, @isrngops X op1 op2.
Definition ConstructiveRing_set (X : ConstructiveRing) : apsetwith2binop := pr1 X.
Definition ConstructiveRing_rng : ConstructiveRing -> rng :=
  λ X : ConstructiveRing, (apsetwith2binop_setwith2binop (ConstructiveRing_set X)),, pr2 X.
Coercion ConstructiveRing_rng : ConstructiveRing >-> rng.

(** Lemmas *)

Section CRing_pty.

Context {X : ConstructiveRing}.

Lemma apCRingplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCRingmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CRingzero_CRingplus :
  forall x : X, 0 + x = x.
Proof.
  now apply rnglunax1.
Qed.
Lemma isrunit_CRingzero_CRingplus :
  forall x : X, x + 0 = x.
Proof.
  now apply rngrunax1.
Qed.
Lemma isassoc_CRingplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rngassoc1.
Qed.
Lemma islinv_CRingopp :
  ∀ x : X, - x + x = 0.
Proof.
  now apply rnglinvax1.
Qed.
Lemma isrinv_CRingopp :
  ∀ x : X, x + - x = 0.
Proof.
  now apply rngrinvax1.
Qed.
Lemma iscomm_CRingplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rngcomm1.
Qed.
Lemma islunit_CRingone_CRingmult :
  forall x : X, 1 * x = x.
Proof.
  now apply rnglunax2.
Qed.
Lemma isrunit_CRingone_CRingmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rngrunax2.
Qed.
Lemma isassoc_CRingmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rngassoc2.
Qed.
Lemma isldistr_CRingplus_CRingmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rngdistraxs.
Qed.

End CRing_pty.

(** ** Constructive commutative ring *)

Definition ConstructiveCommutativeRing := Σ X : apsetwith2binop, @iscommrngops X op1 op2.
Definition ConstructiveCommutativeRing_CommutativeRing :
  ConstructiveCommutativeRing -> ConstructiveRing :=
  λ X : ConstructiveCommutativeRing, pr1 X,, pr1 (pr2 X).
Coercion ConstructiveCommutativeRing_CommutativeRing : ConstructiveCommutativeRing >-> ConstructiveRing.
Definition ConstructiveCommutativeRing_ConstructiveCommutativeRig :
  ConstructiveCommutativeRing -> ConstructiveCommutativeRig :=
  λ X : ConstructiveCommutativeRing, pr1 X,, (iscommrngopstoiscommrigops _ _ _ (pr2 X)).
Coercion ConstructiveCommutativeRing_ConstructiveCommutativeRig : ConstructiveCommutativeRing >-> ConstructiveCommutativeRig.
Definition ConstructiveCommutativeRing_commrng :
  ConstructiveCommutativeRing -> commrng :=
  λ X : ConstructiveCommutativeRing, (apsetwith2binop_setwith2binop (pr1 X)),, (pr2 X).
Coercion ConstructiveCommutativeRing_commrng : ConstructiveCommutativeRing >-> commrng.

(** Lemmas *)

Section CCRing_pty.

Context {X : ConstructiveCommutativeRing}.

Lemma apCCRingplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCCRingmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CCRingzero_CCRingplus :
  forall x : X, 0 + x = x.
Proof.
  now apply rnglunax1.
Qed.
Lemma isrunit_CCRingzero_CCRingplus :
  forall x : X, x + 0 = x.
Proof.
  now apply rngrunax1.
Qed.
Lemma isassoc_CCRingplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rngassoc1.
Qed.
Lemma islinv_CCRingopp :
  ∀ x : X, - x + x = 0.
Proof.
  now apply rnglinvax1.
Qed.
Lemma isrinv_CCRingopp :
  ∀ x : X, x + - x = 0.
Proof.
  now apply rngrinvax1.
Qed.
Lemma iscomm_CCRingplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rngcomm1.
Qed.
Lemma islunit_CCRingone_CCRingmult :
  forall x : X, 1 * x = x.
Proof.
  now apply rnglunax2.
Qed.
Lemma isrunit_CCRingone_CCRingmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rngrunax2.
Qed.
Lemma isassoc_CCRingmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rngassoc2.
Qed.
Lemma iscomm_CCRingmult :
  forall x y : X, x * y = y * x.
Proof.
  apply (rngcomm2 (ConstructiveCommutativeRing_commrng X)).
Qed.
Lemma isldistr_CCRingplus_CCRingmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rngdistraxs.
Qed.

End CCRing_pty.

(** ** Constructive rig with division *)

Definition isConstrDivRig (X : ConstructiveRig) :=
  isnonzeroCR X × (∀ x : X, x # (0%rig : X) -> multinvpair X x).

Definition ConstructiveDivisionRig := Σ X : ConstructiveRig, isConstrDivRig X.
Definition ConstructiveDivisionRig_ConstructiveRig : ConstructiveDivisionRig -> ConstructiveRig := pr1.
Coercion ConstructiveDivisionRig_ConstructiveRig : ConstructiveDivisionRig >-> ConstructiveRig.

Definition CDRinv {X : ConstructiveDivisionRig} (x : X) (Hx0 : x # (0%rig : X)) : X :=
  (pr1 (pr2 (pr2 X) x Hx0)).
Definition CDRdiv {X : ConstructiveDivisionRig} (x y : X) (Hy0 : y # (0%rig : X)) : X :=
  (x * CDRinv y Hy0).

Notation "/ x" := (CDRinv (pr1 x) (pr2 x)).
Notation "x / y" := (CDRdiv x (pr1 y) (pr2 y)).

(** Lemmas *)

Section CDR_pty.

Context {X : ConstructiveDivisionRig}.

Lemma isnonzeroCDR : (1%rig : X) # (0%rig : X).
Proof.
  exact (pr1 (pr2 X)).
Qed.
Lemma apCDRplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCDRmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CDRzero_CDRplus :
  forall x : X, 0%rig + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CDRzero_CDRplus :
  forall x : X, x + 0%rig = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CDRplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CDRplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CDRone_CDRmult :
  forall x : X, 1%rig * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CDRone_CDRmult :
  forall x : X, x * 1%rig = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CDRmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma islinv_CDRinv :
  ∀ (x : X) (Hx0 : x # (0%rig : X)),
    (CDRinv x Hx0) * x = 1%rig.
Proof.
  intros x Hx0.
  apply (pr1 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma islinv_CDRinv' :
  ∀ (x : Σ x : X, x # (0%rig : X)),
    / x * (pr1 x) = 1%rig.
Proof.
  intros x.
  now apply islinv_CDRinv.
Qed.
Lemma isrinv_CDRinv :
  ∀ (x : X) (Hx0 : x # (0%rig : X)),
    x * (CDRinv x Hx0) = 1%rig.
Proof.
  intros x Hx0.
  apply (pr2 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma isrinv_CDRinv' :
  ∀ (x : Σ x : X, x # (0%rig : X)),
    (pr1 x) * / x = 1%rig.
Proof.
  intros x.
  now apply isrinv_CDRinv.
Qed.
Lemma islabsorb_CDRzero_CDRmult :
  ∀ x : X, 0%rig * x = 0%rig.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CDRzero_CDRmult :
  ∀ x : X, x * 0%rig = 0%rig.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CDRplus_CDRmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Print invpair.

End CDR_pty.

(** ** Constructive commutative rig with division *)

Definition ConstructiveCommutativeDivisionRig := Σ X : ConstructiveCommutativeRig, isConstrDivRig X.

(** ** Constructive Field *)

Definition ConstructiveField := Σ X : ConstructiveCommutativeRing, isConstrDivRig X.
