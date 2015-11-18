(** * Definition of appartness relationConstructive Algebraic Structures *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Foundations.Algebra.DivisionRig.
Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

(** ** Constructive rig *)

Definition ConstructiveRig :=
  Σ X : apsetwith2binop, @isrigops X op1 op2.
Arguments ConstructiveRig: simpl never.
Definition ConstructiveRig_set (X : ConstructiveRig) : apsetwith2binop := pr1 X.
Arguments ConstructiveRig_set X : simpl never.
Definition ConstructiveRig_rig : ConstructiveRig -> rig :=
  λ X : ConstructiveRig, (apsetwith2binop_setwith2binop (ConstructiveRig_set X)),, pr2 X.
Coercion ConstructiveRig_rig : ConstructiveRig >-> rig.
Arguments ConstructiveRig_rig: simpl never.

Delimit Scope CRig_scope with CRig.

Definition CRigap {X : ConstructiveRig} : hrel X := λ x y : X, (x # y)%tap.
Arguments CRigap: simpl never.
Definition CRigzero {X : ConstructiveRig} : X := 0%rig.
Arguments CRigzero: simpl never.
Definition CRigone {X : ConstructiveRig} : X := 1%rig.
Arguments CRigone: simpl never.
Definition CRigplus {X : ConstructiveRig} : binop X := λ x y : X, (op1 x y).
Arguments CRigplus: simpl never.
Definition CRigmult {X : ConstructiveRig} : binop X := λ x y : X, (op2 x y)%rig.
Arguments CRigmult: simpl never.

Open Scope CRig_scope.

Notation "x # y" := (CRigap x y) : CRig_scope.
Notation "0" := CRigzero : CRig_scope.
Notation "1" := CRigone : CRig_scope.
Notation "x + y" := (CRigplus x y) : CRig_scope.
Notation "x * y" := (CRigmult x y) : CRig_scope.

Definition isnonzeroCR (X : ConstructiveRig) := (1 : X) # (0 : X).
Definition isConstrDivRig (X : ConstructiveRig) :=
  isnonzeroCR X × (∀ x : X, x # 0 -> multinvpair X x).

(** Lemmas *)

Section CRig_pty.

Context {X : ConstructiveRig}.

Lemma apCRigplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  simpl.
  exact isapbinop_op1.
Qed.
Lemma apCRigmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CRigzero_CRigplus :
  forall x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CRigzero_CRigplus :
  forall x : X, x + 0 = x.
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
  forall x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CRigone_CRigmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CRigmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma islabsorb_CRigzero_CRigmult :
  ∀ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CRigzero_CRigmult :
  ∀ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CRigplus_CRigmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Lemma CRigmultapCRigzero :
  forall x y : X, x * y # 0 -> x # 0 ∧ y # 0.
Proof.
  intros x y Hmult.
  split.
  - apply islapbinop_op2 with y.
    change (op2 0 y)%tap with (0 * y).
    now rewrite islabsorb_CRigzero_CRigmult.
  - apply israpbinop_op2 with x.
    change (op2 x 0) with (x * 0).
    now rewrite israbsorb_CRigzero_CRigmult.
Qed.

End CRig_pty.

Close Scope CRig_scope.

(** ** Constructive commutative rig *)

Definition ConstructiveCommutativeRig :=
  Σ X : apsetwith2binop, @iscommrigops X op1 op2.
Definition ConstructiveCommutativeRig_ConstructiveRig (X : ConstructiveCommutativeRig) : ConstructiveRig :=
  pr1 X,, pr1 (pr2 X).
Coercion ConstructiveCommutativeRig_ConstructiveRig : ConstructiveCommutativeRig >-> ConstructiveRig.
Definition ConstructiveCommutativeRig_commrig : ConstructiveCommutativeRig -> commrig :=
  λ X : ConstructiveCommutativeRig, (apsetwith2binop_setwith2binop (ConstructiveRig_set X)),, pr2 X.

Definition CCRigap {X : ConstructiveCommutativeRig} : hrel X := λ x y : X, (x # y)%tap.
Definition CCRigzero {X : ConstructiveCommutativeRig} : X := 0%rig.
Definition CCRigone {X : ConstructiveCommutativeRig} : X := 1%rig.
Definition CCRigplus {X : ConstructiveCommutativeRig} : binop X := λ x y : X, (x + y)%rig.
Definition CCRigmult {X : ConstructiveCommutativeRig} : binop X := λ x y : X, (x * y)%rig.

Delimit Scope CCRig_scope with CCRig.
Open Scope CCRig_scope.

Notation "x # y" := (CCRigap x y) : CCRig_scope.
Notation "0" := CCRigzero : CCRig_scope.
Notation "1" := CCRigone : CCRig_scope.
Notation "x + y" := (CCRigplus x y) : CCRig_scope.
Notation "x * y" := (CCRigmult x y) : CCRig_scope.

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
  forall x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CCRigzero_CCRigplus :
  forall x : X, x + 0 = x.
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
  forall x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CCRigone_CCRigmult :
  forall x : X, x * 1 = x.
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
  ∀ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CCRigzero_CCRigmult :
  ∀ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CCRigplus_CCRigmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Close Scope CCRig_scope.

End CCRig_pty.

(** ** Constructive ring *)

Definition ConstructiveRing := Σ X : apsetwith2binop, @isrngops X op1 op2.
Definition ConstructiveRing_set (X : ConstructiveRing) : apsetwith2binop := pr1 X.
Definition ConstructiveRing_rng : ConstructiveRing -> rng :=
  λ X : ConstructiveRing, (apsetwith2binop_setwith2binop (ConstructiveRing_set X)),, pr2 X.
Coercion ConstructiveRing_rng : ConstructiveRing >-> rng.

Definition CRingap {X : ConstructiveRing} : hrel X := λ x y : X, (x # y)%tap.
Definition CRingzero {X : ConstructiveRing} : X := 0%rng.
Definition CRingone {X : ConstructiveRing} : X := 1%rng.
Definition CRingplus {X : ConstructiveRing} : binop X := λ x y : X, (x + y)%rng.
Definition CRingop {X : ConstructiveRing} : unop X := λ x : X, (- x)%rng.
Definition CRingminus {X : ConstructiveRing} : binop X := λ x y : X, CRingplus x (CRingop y).
Definition CRingmult {X : ConstructiveRing} : binop X := λ x y : X, (x * y)%rng.

Delimit Scope CRing_scope with CRing.
Open Scope CRing_scope.

Notation "x # y" := (CRingap x y) : CRing_scope.
Notation "0" := CRingzero : CRing_scope.
Notation "1" := CRingone : CRing_scope.
Notation "x + y" := (CRingplus x y) : CRing_scope.
Notation "- x" := (CRingop x) : CRing_scope.
Notation "x - y" := (x + (- y)) : CRing_scope.
Notation "x * y" := (CRingmult x y) : CRing_scope.

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

Close Scope CRing_scope.

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

Definition CCRingap {X : ConstructiveCommutativeRing} : hrel X := λ x y : X, (x # y)%tap.
Definition CCRingzero {X : ConstructiveCommutativeRing} : X := 0%rng.
Definition CCRingone {X : ConstructiveCommutativeRing} : X := 1%rng.
Definition CCRingplus {X : ConstructiveCommutativeRing} : binop X := λ x y : X, (x + y)%rng.
Definition CCRingop {X : ConstructiveCommutativeRing} : unop X := λ x : X, (- x)%rng.
Definition CCRingminus {X : ConstructiveCommutativeRing} : binop X := λ x y : X, CCRingplus x (CCRingop y).
Definition CCRingmult {X : ConstructiveCommutativeRing} : binop X := λ x y : X, (x * y)%rng.

Delimit Scope CCRing_scope with CCRing.
Open Scope CCRing_scope.

Notation "x # y" := (CCRingap x y) : CCRing_scope.
Notation "0" := CCRingzero : CCRing_scope.
Notation "1" := CCRingone : CCRing_scope.
Notation "x + y" := (CCRingplus x y) : CCRing_scope.
Notation "- x" := (CCRingop x) : CCRing_scope.
Notation "x - y" := (x + (- y)) : CCRing_scope.
Notation "x * y" := (CCRingmult x y) : CCRing_scope.

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

Close Scope CCRing_scope.

End CCRing_pty.

(** ** Constructive rig with division *)

Definition ConstructiveDivisionRig := Σ X : ConstructiveRig, isConstrDivRig X.
Definition ConstructiveDivisionRig_ConstructiveRig : ConstructiveDivisionRig -> ConstructiveRig := pr1.
Coercion ConstructiveDivisionRig_ConstructiveRig : ConstructiveDivisionRig >-> ConstructiveRig.

Definition CDRap {X : ConstructiveDivisionRig} : hrel X := λ x y : X, (x # y)%tap.
Definition CDRzero {X : ConstructiveDivisionRig} : X := 0%rig.
Definition CDRone {X : ConstructiveDivisionRig} : X := 1%rig.
Definition CDRplus {X : ConstructiveDivisionRig} : binop X := λ x y : X, op1 x y.
Definition CDRmult {X : ConstructiveDivisionRig} : binop X := λ x y : X, op2 x y.

Delimit Scope CDR_scope with CDR.
Open Scope CDR_scope.

Notation "x # y" := (CDRap x y) : CDR_scope.
Notation "0" := CDRzero : CDR_scope.
Notation "1" := CDRone : CDR_scope.
Notation "x + y" := (CDRplus x y) : CDR_scope.
Notation "x * y" := (CDRmult x y) : CDR_scope.

Definition CDRinv {X : ConstructiveDivisionRig} (x : X) (Hx0 : x # 0) : X :=
  (pr1 (pr2 (pr2 X) x Hx0)).
Definition CDRdiv {X : ConstructiveDivisionRig} (x y : X) (Hy0 : y # 0) : X :=
  CDRmult x (CDRinv y Hy0).

(** Lemmas *)

Section CDR_pty.

Context {X : ConstructiveDivisionRig}.

Lemma isnonzeroCDR : (1 : X) # (0 : X).
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
  forall x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CDRzero_CDRplus :
  forall x : X, x + 0 = x.
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
  forall x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CDRone_CDRmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CDRmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma islinv_CDRinv :
  ∀ (x : X) (Hx0 : x # (0 : X)),
    (CDRinv x Hx0) * x = 1.
Proof.
  intros x Hx0.
  apply (pr1 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma isrinv_CDRinv :
  ∀ (x : X) (Hx0 : x # (0 : X)),
    x * (CDRinv x Hx0) = 1.
Proof.
  intros x Hx0.
  apply (pr2 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma islabsorb_CDRzero_CDRmult :
  ∀ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CDRzero_CDRmult :
  ∀ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CDRplus_CDRmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Close Scope CDR_scope.

End CDR_pty.

(** ** Constructive commutative rig with division *)

Definition ConstructiveCommutativeDivisionRig := Σ X : ConstructiveCommutativeRig, isConstrDivRig X.
Definition ConstructiveCommutativeDivisionRig_ConstructiveCommutativeRig :
  ConstructiveCommutativeDivisionRig -> ConstructiveCommutativeRig := pr1.
Coercion ConstructiveCommutativeDivisionRig_ConstructiveCommutativeRig :
  ConstructiveCommutativeDivisionRig >-> ConstructiveCommutativeRig.
Definition ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig :
  ConstructiveCommutativeDivisionRig -> ConstructiveDivisionRig :=
  λ X, (ConstructiveCommutativeRig_ConstructiveRig (pr1 X)) ,, (pr2 X).
Coercion ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig :
  ConstructiveCommutativeDivisionRig >-> ConstructiveDivisionRig.

Definition CCDRap {X : ConstructiveCommutativeDivisionRig} : hrel X := λ x y : X, (x # y)%tap.
Definition CCDRzero {X : ConstructiveCommutativeDivisionRig} : X := 0%rig.
Definition CCDRone {X : ConstructiveCommutativeDivisionRig} : X := 1%rig.
Definition CCDRplus {X : ConstructiveCommutativeDivisionRig} : binop X := λ x y : X, op1 x y.
Definition CCDRmult {X : ConstructiveCommutativeDivisionRig} : binop X := λ x y : X, op2 x y.

Delimit Scope CCDR_scope with CCDR.
Open Scope CCDR_scope.

Notation "x # y" := (CCDRap x y) : CCDR_scope.
Notation "0" := CCDRzero : CCDR_scope.
Notation "1" := CCDRone : CCDR_scope.
Notation "x + y" := (CCDRplus x y) : CCDR_scope.
Notation "x * y" := (CCDRmult x y) : CCDR_scope.

Definition CCDRinv {X : ConstructiveCommutativeDivisionRig} (x : X) (Hx0 : x # CCDRzero) : X :=
  CDRinv (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X) x Hx0.
Definition CCDRdiv {X : ConstructiveCommutativeDivisionRig} (x y : X) (Hy0 : y # CCDRzero) : X :=
  CCDRmult x (CCDRinv y Hy0).

(** Lemmas *)

Section CCDR_pty.

Context {X : ConstructiveCommutativeDivisionRig}.

Lemma isnonzeroCCDR : (1 : X) # (0 : X).
Proof.
  exact (pr1 (pr2 X)).
Qed.
Lemma apCCDRplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCCDRmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CCDRzero_CCDRplus :
  forall x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CCDRzero_CCDRplus :
  forall x : X, x + 0 = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CCDRplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CCDRplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CCDRone_CCDRmult :
  forall x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CCDRone_CCDRmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CCDRmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma iscomm_CCDRmult :
  forall x y : X, x * y = y * x.
Proof.
  now apply (rigcomm2 (ConstructiveCommutativeRig_commrig X)).
Qed.
Lemma islinv_CCDRinv :
  ∀ (x : X) (Hx0 : x # (0 : X)),
    (CDRinv (X := X) x Hx0) * x = 1.
Proof.
  intros x Hx0.
  apply (pr1 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma isrinv_CCDRinv :
  ∀ (x : X) (Hx0 : x # (0 : X)),
    x * (CDRinv (X := X) x Hx0) = 1.
Proof.
  intros x Hx0.
  apply (pr2 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma islabsorb_CCDRzero_CCDRmult :
  ∀ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CCDRzero_CCDRmult :
  ∀ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CCDRplus_CCDRmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Close Scope CCDR_scope.

End CCDR_pty.

(** ** Constructive Field *)

Definition ConstructiveField := Σ X : ConstructiveCommutativeRing, isConstrDivRig X.
Definition ConstructiveField_ConstructiveCommutativeRing :
  ConstructiveField -> ConstructiveCommutativeRing := pr1.
Coercion ConstructiveField_ConstructiveCommutativeRing :
  ConstructiveField >-> ConstructiveCommutativeRing.
Definition ConstructiveField_ConstructiveCommutativeDivisionRig :
  ConstructiveField -> ConstructiveCommutativeDivisionRig :=
  λ X, (ConstructiveCommutativeRing_ConstructiveCommutativeRig (pr1 X)) ,, (pr2 X).
Coercion ConstructiveField_ConstructiveCommutativeDivisionRig :
  ConstructiveField >-> ConstructiveCommutativeDivisionRig.

Definition CFap {X : ConstructiveField} : hrel X := λ x y : X, (x # y)%tap.
Definition CFzero {X : ConstructiveField} : X := 0%rng.
Definition CFone {X : ConstructiveField} : X := 1%rng.
Definition CFplus {X : ConstructiveField} : binop X := λ x y : X, op1 x y.
Definition CFopp {X : ConstructiveField} : unop X := λ x : X, (- x)%rng.
Definition CFminus {X : ConstructiveField} : binop X := λ x y : X, CFplus x (CFopp y).
Definition CFmult {X : ConstructiveField} : binop X := λ x y : X, op2 x y.

Delimit Scope CF_scope with CF.
Open Scope CF_scope.

Notation "x # y" := (CFap x y) : CF_scope.
Notation "0" := CFzero : CF_scope.
Notation "1" := CFone : CF_scope.
Notation "x + y" := (CFplus x y) : CF_scope.
Notation "- x" := (CFopp x) : CF_scope.
Notation "x - y" := (x + (- y)) : CF_scope.
Notation "x * y" := (CFmult x y) : CF_scope.

Definition CFinv {X : ConstructiveField} (x : X) (Hx0 : x # CFzero) : X :=
  CCDRinv (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) x Hx0.
Definition CFdiv {X : ConstructiveField} (x y : X) (Hy0 : y # CFzero) : X :=
  CFmult x (CFinv y Hy0).

(** Lemmas *)

Section CF_pty.

Context {X : ConstructiveField}.

Lemma isnonzeroCF : (1 : X) # (0 : X).
Proof.
  exact (pr1 (pr2 X)).
Qed.
Lemma apCFplus :
  forall x x' y y' : X,
    x + y # x' + y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op1.
Qed.
Lemma apCFmult :
  forall x x' y y' : X,
    x * y # x' * y' -> x # x' ∨ y # y'.
Proof.
  exact isapbinop_op2.
Qed.

Lemma islunit_CFzero_CFplus :
  forall x : X, 0 + x = x.
Proof.
  now apply rnglunax1.
Qed.
Lemma isrunit_CFzero_CFplus :
  forall x : X, x + 0 = x.
Proof.
  now apply rngrunax1.
Qed.
Lemma isassoc_CFplus :
  forall x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rngassoc1.
Qed.
Lemma islinv_CFopp :
  ∀ x : X, - x + x = 0.
Proof.
  now apply rnglinvax1.
Qed.
Lemma isrinv_CFopp :
  ∀ x : X, x + - x = 0.
Proof.
  now apply rngrinvax1.
Qed.

Lemma iscomm_CFplus :
  forall x y : X, x + y = y + x.
Proof.
  now apply rngcomm1.
Qed.
Lemma islunit_CFone_CFmult :
  forall x : X, 1 * x = x.
Proof.
  now apply rnglunax2.
Qed.
Lemma isrunit_CFone_CFmult :
  forall x : X, x * 1 = x.
Proof.
  now apply rngrunax2.
Qed.
Lemma isassoc_CFmult :
  forall x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rngassoc2.
Qed.
Lemma iscomm_CFmult :
  forall x y : X, x * y = y * x.
Proof.
  now apply (rngcomm2 (ConstructiveCommutativeRing_commrng X)).
Qed.
Lemma islinv_CFinv :
  ∀ (x : X) (Hx0 : x # 0),
    (CFinv x Hx0) * x = 1.
Proof.
  intros x Hx0.
  apply (pr1 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma isrinv_CFinv :
  ∀ (x : X) (Hx0 : x # 0),
    x * (CFinv x Hx0) = 1.
Proof.
  intros x Hx0.
  apply (pr2 (pr2 (pr2 (pr2 X) x Hx0))).
Qed.
Lemma islabsorb_CFzero_CFmult :
  ∀ x : X, 0 * x = 0.
Proof.
  now apply rngmult0x.
Qed.
Lemma israbsorb_CFzero_CFmult :
  ∀ x : X, x * 0 = 0.
Proof.
  now apply rngmultx0.
Qed.
Lemma isldistr_CFplus_CFmult :
  ∀ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rngdistraxs.
Qed.

End CF_pty.

Close Scope CF_scope.
