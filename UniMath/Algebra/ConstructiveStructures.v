(** * Definition of appartness relationConstructive Algebraic Structures *)
(** Catherine Lelay. Sep. 2015 *)

Unset Kernel Term Sharing.

Require Export UniMath.Algebra.Apartness.
Require Export UniMath.Algebra.DivisionRig.
Require Export UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.MoreFoundations.Tactics.

(** ** Predicats in a rig with a tight appartness relation *)

Definition isnonzeroCR (X : rig) (R : tightap X) := R 1%rig 0%rig.
Definition isConstrDivRig (X : rig) (R : tightap X) :=
  isnonzeroCR X R × (∏ x : X, R x 0%rig -> multinvpair X x).

(** ** Constructive rig with division *)

Definition ConstructiveDivisionRig :=
  ∑ X : rig,
  ∑ R : tightap X,
        isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op1
      × isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op2
      × isConstrDivRig X R.
Definition ConstructiveDivisionRig_rig : ConstructiveDivisionRig -> rig := pr1.
Coercion ConstructiveDivisionRig_rig : ConstructiveDivisionRig >-> rig.
Definition ConstructiveDivisionRig_apsetwith2binop : ConstructiveDivisionRig -> apsetwith2binop.
Proof.
  intros X.
  exists (pr1 (pr1 (pr1 X)),,(pr1 (pr2 X))).
  split.
  exact (_,,(pr1 (pr2 (pr2 X)))).
  exact (_,,(pr1 (pr2 (pr2 (pr2 X))))).
Defined.

Definition CDRap {X : ConstructiveDivisionRig} : hrel X := λ x y : X, (pr1 (pr2 X)) x y.
Definition CDRzero {X : ConstructiveDivisionRig} : X := 0%rig.
Definition CDRone {X : ConstructiveDivisionRig} : X := 1%rig.
Definition CDRplus {X : ConstructiveDivisionRig} : binop X := λ x y : X, op1 (X := ConstructiveDivisionRig_apsetwith2binop X) x y.
Definition CDRmult {X : ConstructiveDivisionRig} : binop X := λ x y : X, op2 (X := ConstructiveDivisionRig_apsetwith2binop X) x y.

(* Declare Scope CDR_scope. *)
Delimit Scope CDR_scope with CDR.
Local Open Scope CDR_scope.

Notation "x ≠ y" := (CDRap x y) (at level 70, no associativity) : CDR_scope.
Notation "0" := CDRzero : CDR_scope.
Notation "1" := CDRone : CDR_scope.
Notation "x + y" := (CDRplus x y) : CDR_scope.
Notation "x * y" := (CDRmult x y) : CDR_scope.

Definition CDRinv {X : ConstructiveDivisionRig} (x : X) (Hx0 : x ≠ 0) : X :=
  (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))) x Hx0)).
Definition CDRdiv {X : ConstructiveDivisionRig} (x y : X) (Hy0 : y ≠ 0) : X :=
  CDRmult x (CDRinv y Hy0).

(** Lemmas *)

Section CDR_pty.

Context {X : ConstructiveDivisionRig}.

Lemma isirrefl_CDRap :
  ∏ x : X, ¬ (x ≠ x).
Proof.
  exact (pr1 (pr1 (pr2 (pr1 (pr2 X))))).
Qed.
Lemma issymm_CDRap :
  ∏ x y : X, x ≠ y -> y ≠ x.
Proof.
  exact (pr1 (pr2 (pr1 (pr2 (pr1 (pr2 X)))))).
Qed.
Lemma iscotrans_CDRap :
  ∏ x y z : X, x ≠ z -> x ≠ y ∨ y ≠ z.
Proof.
  exact (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 X)))))).
Qed.
Lemma istight_CDRap :
  ∏ x y : X, ¬ (x ≠ y) -> x = y.
Proof.
  exact (pr2 (pr2 (pr1 (pr2 X)))).
Qed.

Lemma isnonzeroCDR : (1 : X) ≠ (0 : X).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma islunit_CDRzero_CDRplus :
  ∏ x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CDRzero_CDRplus :
  ∏ x : X, x + 0 = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CDRplus :
  ∏ x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CDRplus :
  ∏ x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CDRone_CDRmult :
  ∏ x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CDRone_CDRmult :
  ∏ x : X, x * 1 = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CDRmult :
  ∏ x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma islinv_CDRinv :
  ∏ (x : X) (Hx0 : x ≠ (0 : X)),
    (CDRinv x Hx0) * x = 1.
Proof.
  intros x Hx0.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))) x Hx0))).
Qed.
Lemma isrinv_CDRinv :
  ∏ (x : X) (Hx0 : x ≠ (0 : X)),
    x * (CDRinv x Hx0) = 1.
Proof.
  intros x Hx0.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))) x Hx0))).
Qed.
Lemma islabsorb_CDRzero_CDRmult :
  ∏ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CDRzero_CDRmult :
  ∏ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CDRplus_CDRmult :
  ∏ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.

Lemma apCDRplus :
  ∏ x x' y y' : X,
    x + y ≠ x' + y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (isapbinop_op1 (X := ConstructiveDivisionRig_apsetwith2binop X)).
Qed.
Lemma CDRplus_apcompat_l :
  ∏ x y z : X, y + x ≠ z + x -> y ≠ z.
Proof.
  intros x y z.
  exact (islapbinop_op1 (X := ConstructiveDivisionRig_apsetwith2binop X) _ _ _).
Qed.
Lemma CDRplus_apcompat_r :
  ∏ x y z : X, x + y ≠ x + z -> y ≠ z.
Proof.
  exact (israpbinop_op1 (X := ConstructiveDivisionRig_apsetwith2binop X)).
Qed.

Lemma apCDRmult :
  ∏ x x' y y' : X,
    x * y ≠ x' * y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (isapbinop_op2 (X := ConstructiveDivisionRig_apsetwith2binop X)).
Qed.
Lemma CDRmult_apcompat_l :
  ∏ x y z : X, y * x ≠ z * x -> y ≠ z.
Proof.
  intros x y z.
  exact (islapbinop_op2 (X := ConstructiveDivisionRig_apsetwith2binop X) _ _ _).
Qed.
Lemma CDRmult_apcompat_l' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> y * x ≠ z * x.
Proof.
  intros x y z Hx Hap.
  refine (CDRmult_apcompat_l (CDRinv x Hx) _ _ _).
  rewrite !isassoc_CDRmult, isrinv_CDRinv, !isrunit_CDRone_CDRmult.
  exact Hap.
Qed.
Lemma CDRmult_apcompat_r :
  ∏ x y z : X, x * y ≠ x * z -> y ≠ z.
Proof.
  exact (israpbinop_op2 (X := ConstructiveDivisionRig_apsetwith2binop X)).
Qed.
Lemma CDRmult_apcompat_r' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> x * y ≠ x * z.
Proof.
  intros x y z Hx Hap.
  refine (CDRmult_apcompat_r (CDRinv x Hx) _ _ _).
  rewrite <- !isassoc_CDRmult, islinv_CDRinv, !islunit_CDRone_CDRmult.
  exact Hap.
Qed.

Lemma CDRmultapCDRzero :
  ∏ x y : X, x * y ≠ 0 -> x ≠ 0 ∧ y ≠ 0.
Proof.
  intros x y Hmult.
  split.
  - apply CDRmult_apcompat_l with y.
    rewrite islabsorb_CDRzero_CDRmult.
    exact Hmult.
  - apply CDRmult_apcompat_r with x.
    rewrite israbsorb_CDRzero_CDRmult.
    exact Hmult.
Qed.

Close Scope CDR_scope.

End CDR_pty.

(** ** Constructive commutative rig with division *)

Definition ConstructiveCommutativeDivisionRig :=
  ∑ X : commrig,
  ∑ R : tightap X,
        isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op1
      × isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op2
      × isConstrDivRig X R.
Definition ConstructiveCommutativeDivisionRig_commrig :
  ConstructiveCommutativeDivisionRig -> commrig := pr1.
Coercion ConstructiveCommutativeDivisionRig_commrig :
  ConstructiveCommutativeDivisionRig >-> commrig.

Definition ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig :
  ConstructiveCommutativeDivisionRig -> ConstructiveDivisionRig :=
  λ X, (pr1 (pr1 X),,pr1 (pr2 (pr1 X))) ,, (pr2 X).
Coercion ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig :
  ConstructiveCommutativeDivisionRig >-> ConstructiveDivisionRig.

Definition CCDRap {X : ConstructiveCommutativeDivisionRig} : hrel X := λ x y : X, CDRap (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X) x y.
Definition CCDRzero {X : ConstructiveCommutativeDivisionRig} : X := 0%rig.
Definition CCDRone {X : ConstructiveCommutativeDivisionRig} : X := 1%rig.
Definition CCDRplus {X : ConstructiveCommutativeDivisionRig} : binop X := λ x y : X, CDRplus (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X) x y.
Definition CCDRmult {X : ConstructiveCommutativeDivisionRig} : binop X := λ x y : X, CDRmult (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X) x y.

(* Declare Scope CCDR_scope. *)
Delimit Scope CCDR_scope with CCDR.
Local Open Scope CCDR_scope.

Notation "x ≠ y" := (CCDRap x y) (at level 70, no associativity) : CCDR_scope.
Notation "0" := CCDRzero : CCDR_scope.
Notation "1" := CCDRone : CCDR_scope.
Notation "x + y" := (CCDRplus x y) : CCDR_scope.
Notation "x * y" := (CCDRmult x y) : CCDR_scope.

Definition CCDRinv {X : ConstructiveCommutativeDivisionRig} (x : X) (Hx0 : x ≠ CCDRzero) : X :=
  CDRinv (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X) x Hx0.
Definition CCDRdiv {X : ConstructiveCommutativeDivisionRig} (x y : X) (Hy0 : y ≠ CCDRzero) : X :=
  CCDRmult x (CCDRinv y Hy0).

(** Lemmas *)

Section CCDR_pty.

Context {X : ConstructiveCommutativeDivisionRig}.

Lemma isirrefl_CCDRap :
  ∏ x : X, ¬ (x ≠ x).
Proof.
  exact (isirrefl_CDRap (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma issymm_CCDRap :
  ∏ x y : X, x ≠ y -> y ≠ x.
Proof.
  exact (issymm_CDRap (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma iscotrans_CCDRap :
  ∏ x y z : X, x ≠ z -> x ≠ y ∨ y ≠ z.
Proof.
  exact (iscotrans_CDRap (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma istight_CCDRap :
  ∏ x y : X, ¬ (x ≠ y) -> x = y.
Proof.
  exact (istight_CDRap (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.

Lemma isnonzeroCCDR : (1 : X) ≠ (0 : X).
Proof.
  exact isnonzeroCDR.
Qed.

Lemma islunit_CCDRzero_CCDRplus :
  ∏ x : X, 0 + x = x.
Proof.
  now apply riglunax1.
Qed.
Lemma isrunit_CCDRzero_CCDRplus :
  ∏ x : X, x + 0 = x.
Proof.
  now apply rigrunax1.
Qed.
Lemma isassoc_CCDRplus :
  ∏ x y z : X, x + y + z = x + (y + z).
Proof.
  now apply rigassoc1.
Qed.
Lemma iscomm_CCDRplus :
  ∏ x y : X, x + y = y + x.
Proof.
  now apply rigcomm1.
Qed.
Lemma islunit_CCDRone_CCDRmult :
  ∏ x : X, 1 * x = x.
Proof.
  now apply riglunax2.
Qed.
Lemma isrunit_CCDRone_CCDRmult :
  ∏ x : X, x * 1 = x.
Proof.
  now apply rigrunax2.
Qed.
Lemma isassoc_CCDRmult :
  ∏ x y z : X, x * y * z = x * (y * z).
Proof.
  now apply rigassoc2.
Qed.
Lemma iscomm_CCDRmult :
  ∏ x y : X, x * y = y * x.
Proof.
  now apply rigcomm2.
Qed.
Lemma islinv_CCDRinv :
  ∏ (x : X) (Hx0 : x ≠ (0 : X)),
    (CDRinv (X := X) x Hx0) * x = 1.
Proof.
  exact (islinv_CDRinv (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma isrinv_CCDRinv :
  ∏ (x : X) (Hx0 : x ≠ (0 : X)),
    x * (CDRinv (X := X) x Hx0) = 1.
Proof.
  exact (isrinv_CDRinv (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma islabsorb_CCDRzero_CCDRmult :
  ∏ x : X, 0 * x = 0.
Proof.
  now apply rigmult0x.
Qed.
Lemma israbsorb_CCDRzero_CCDRmult :
  ∏ x : X, x * 0 = 0.
Proof.
  now apply rigmultx0.
Qed.
Lemma isldistr_CCDRplus_CCDRmult :
  ∏ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply rigdistraxs.
Qed.
Lemma isrdistr_CCDRplus_CCDRmult :
  ∏ x y z : X, (x + y) * z = x * z + y * z.
Proof.
  intros x y z.
  rewrite !(iscomm_CCDRmult _ z).
  now apply rigdistraxs.
Qed.

Lemma apCCDRplus :
  ∏ x x' y y' : X,
    x + y ≠ x' + y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (apCDRplus (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRplus_apcompat_l :
  ∏ x y z : X, y + x ≠ z + x -> y ≠ z.
Proof.
  exact (CDRplus_apcompat_l (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRplus_apcompat_r :
  ∏ x y z : X, x + y ≠ x + z -> y ≠ z.
Proof.
  exact (CDRplus_apcompat_r (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.

Lemma apCCDRmult :
  ∏ x x' y y' : X,
    x * y ≠ x' * y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (apCDRmult (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRmult_apcompat_l :
  ∏ x y z : X, y * x ≠ z * x -> y ≠ z.
Proof.
  exact (CDRmult_apcompat_l (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRmult_apcompat_l' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> y * x ≠ z * x.
Proof.
  exact (CDRmult_apcompat_l' (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRmult_apcompat_r :
  ∏ x y z : X, x * y ≠ x * z -> y ≠ z.
Proof.
  exact (CDRmult_apcompat_r (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.
Lemma CCDRmult_apcompat_r' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> x * y ≠ x * z.
Proof.
  exact (CDRmult_apcompat_r' (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.

Lemma CCDRmultapCCDRzero :
  ∏ x y : X, x * y ≠ 0 -> x ≠ 0 ∧ y ≠ 0.
Proof.
  exact (CDRmultapCDRzero (X := ConstructiveCommutativeDivisionRig_ConstructiveDivisionRig X)).
Qed.

Close Scope CCDR_scope.

End CCDR_pty.

(** ** Constructive Field *)

Definition ConstructiveField :=
  ∑ X : commring,
  ∑ R : tightap X,
        isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op1
      × isapbinop (X := (pr1 (pr1 X)) ,, R) BinaryOperations.op2
      × isConstrDivRig X R.
Definition ConstructiveField_commring :
  ConstructiveField -> commring := pr1.
Coercion ConstructiveField_commring :
  ConstructiveField >-> commring.
Definition ConstructiveField_ConstructiveCommutativeDivisionRig :
  ConstructiveField -> ConstructiveCommutativeDivisionRig :=
  λ X, (commringtocommrig (pr1 X)) ,, (pr2 X).
Coercion ConstructiveField_ConstructiveCommutativeDivisionRig :
  ConstructiveField >-> ConstructiveCommutativeDivisionRig.

Definition CFap {X : ConstructiveField} : hrel X := λ x y : X, CCDRap (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) x y.
Definition CFzero {X : ConstructiveField} : X := 0%ring.
Definition CFone {X : ConstructiveField} : X := 1%ring.
Definition CFplus {X : ConstructiveField} : binop X := λ x y : X, CCDRplus (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) x y.
Definition CFopp {X : ConstructiveField} : unop X := λ x : X, (- x)%ring.
Definition CFminus {X : ConstructiveField} : binop X := λ x y : X, CFplus x (CFopp y).
Definition CFmult {X : ConstructiveField} : binop X := λ x y : X, CCDRmult (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) x y.

(* Declare Scope CF_scope. *)
Delimit Scope CF_scope with CF.
Local Open Scope CF_scope.

Notation "x ≠ y" := (CFap x y) (at level 70, no associativity) : CF_scope.
Notation "0" := CFzero : CF_scope.
Notation "1" := CFone : CF_scope.
Notation "x + y" := (CFplus x y) : CF_scope.
Notation "- x" := (CFopp x) : CF_scope.
Notation "x - y" := (CFminus x y) : CF_scope.
Notation "x * y" := (CFmult x y) : CF_scope.

Definition CFinv {X : ConstructiveField} (x : X) (Hx0 : x ≠ CFzero) : X :=
  CCDRinv (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) x Hx0.
Definition CFdiv {X : ConstructiveField} (x y : X) (Hy0 : y ≠ CFzero) : X :=
  CFmult x (CFinv y Hy0).

(** Lemmas *)

Section CF_pty.

Context {X : ConstructiveField}.

Lemma isirrefl_CFap :
  ∏ x : X, ¬ (x ≠ x).
Proof.
  exact (isirrefl_CCDRap (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma issymm_CFap :
  ∏ x y : X, x ≠ y -> y ≠ x.
Proof.
  exact (issymm_CCDRap (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma iscotrans_CFap :
  ∏ x y z : X, x ≠ z -> x ≠ y ∨ y ≠ z.
Proof.
  exact (iscotrans_CCDRap (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma istight_CFap :
  ∏ x y : X, ¬ (x ≠ y) -> x = y.
Proof.
  exact (istight_CCDRap (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.

Lemma isnonzeroCF : (1 : X) ≠ (0 : X).
Proof.
  exact (isnonzeroCCDR (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.

Lemma islunit_CFzero_CFplus :
  ∏ x : X, 0 + x = x.
Proof.
  now apply ringlunax1.
Qed.
Lemma isrunit_CFzero_CFplus :
  ∏ x : X, x + 0 = x.
Proof.
  now apply ringrunax1.
Qed.
Lemma isassoc_CFplus :
  ∏ x y z : X, x + y + z = x + (y + z).
Proof.
  now apply ringassoc1.
Qed.
Lemma islinv_CFopp :
  ∏ x : X, - x + x = 0.
Proof.
  now apply ringlinvax1.
Qed.
Lemma isrinv_CFopp :
  ∏ x : X, x + - x = 0.
Proof.
  now apply ringrinvax1.
Qed.

Lemma iscomm_CFplus :
  ∏ x y : X, x + y = y + x.
Proof.
  now apply ringcomm1.
Qed.
Lemma islunit_CFone_CFmult :
  ∏ x : X, 1 * x = x.
Proof.
  now apply ringlunax2.
Qed.
Lemma isrunit_CFone_CFmult :
  ∏ x : X, x * 1 = x.
Proof.
  now apply ringrunax2.
Qed.
Lemma isassoc_CFmult :
  ∏ x y z : X, x * y * z = x * (y * z).
Proof.
  now apply ringassoc2.
Qed.
Lemma iscomm_CFmult :
  ∏ x y : X, x * y = y * x.
Proof.
  now apply ringcomm2.
Qed.
Lemma islinv_CFinv :
  ∏ (x : X) (Hx0 : x ≠ 0),
    (CFinv x Hx0) * x = 1.
Proof.
  exact (islinv_CCDRinv (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma isrinv_CFinv :
  ∏ (x : X) (Hx0 : x ≠ 0),
    x * (CFinv x Hx0) = 1.
Proof.
  exact (isrinv_CCDRinv (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma islabsorb_CFzero_CFmult :
  ∏ x : X, 0 * x = 0.
Proof.
  now apply ringmult0x.
Qed.
Lemma israbsorb_CFzero_CFmult :
  ∏ x : X, x * 0 = 0.
Proof.
  now apply ringmultx0.
Qed.
Lemma isldistr_CFplus_CFmult :
  ∏ x y z : X, z * (x + y) = z * x + z * y.
Proof.
  now apply ringdistraxs.
Qed.
Lemma isrdistr_CFplus_CFmult :
  ∏ x y z : X, (x + y) * z = x * z + y * z.
Proof.
  intros.
  rewrite !(iscomm_CFmult _ z).
  now apply isldistr_CFplus_CFmult.
Qed.

Lemma apCFplus :
  ∏ x x' y y' : X,
    x + y ≠ x' + y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (apCCDRplus (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma CFplus_apcompat_l :
  ∏ x y z : X, y + x ≠ z + x <-> y ≠ z.
Proof.
  intros x y z.
  split.
  - exact (CCDRplus_apcompat_l (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) _ _ _).
  - intros Hap.
    apply (CCDRplus_apcompat_l (X := ConstructiveField_ConstructiveCommutativeDivisionRig X) (- x)).
    change ((y + x) + - x ≠ (z + x) + - x).
    rewrite !isassoc_CFplus, isrinv_CFopp, !isrunit_CFzero_CFplus.
    exact Hap.
Qed.
Lemma CFplus_apcompat_r :
  ∏ x y z : X, x + y ≠ x + z <-> y ≠ z.
Proof.
  intros x y z.
  rewrite !(iscomm_CFplus x).
  now apply CFplus_apcompat_l.
Qed.

Lemma apCFmult :
  ∏ x x' y y' : X,
    x * y ≠ x' * y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (apCCDRmult (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma CFmult_apcompat_l :
  ∏ x y z : X, y * x ≠ z * x -> y ≠ z.
Proof.
  exact (CCDRmult_apcompat_l (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma CFmult_apcompat_l' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> y * x ≠ z * x.
Proof.
  exact (CCDRmult_apcompat_l' (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma CFmult_apcompat_r :
  ∏ x y z : X, x * y ≠ x * z -> y ≠ z.
Proof.
  exact (CCDRmult_apcompat_r (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.
Lemma CFmult_apcompat_r' :
  ∏ x y z : X, x ≠ 0 -> y ≠ z -> x * y ≠ x * z.
Proof.
  exact (CCDRmult_apcompat_r' (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.

Lemma CFmultapCFzero :
  ∏ x y : X, x * y ≠ 0 -> x ≠ 0 ∧ y ≠ 0.
Proof.
  exact (CCDRmultapCCDRzero (X := ConstructiveField_ConstructiveCommutativeDivisionRig X)).
Qed.

End CF_pty.

Close Scope CF_scope.
