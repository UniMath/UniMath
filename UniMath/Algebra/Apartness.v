(** * Definition of appartness relation *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.DecidablePropositions.

(** ** Additionals theorems about relations *)

Lemma isapropisirrefl {X : UU} (rel : hrel X) :
  isaprop (isirrefl rel).
Proof.
  intros ? rel.
  apply impred_isaprop ; intro.
  now apply isapropneg.
Qed.
Lemma isapropissymm {X : UU} (rel : hrel X) :
  isaprop (issymm rel).
Proof.
  intros ? rel.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply isapropimpl.
  now apply pr2.
Qed.
Lemma isapropiscotrans {X : UU} (rel : hrel X) :
  isaprop (iscotrans rel).
Proof.
  intros ? rel.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply impred_isaprop ; intro z.
  apply isapropimpl.
  now apply pr2.
Qed.

(** ** Apartness *)

Definition isaprel {X : UU} (ap : hrel X) :=
  isirrefl ap × issymm ap × iscotrans ap.

Lemma isaprop_isaprel {X : UU} (ap : hrel X) :
  isaprop (isaprel ap).
Proof.
  intros ? ap.
  apply isapropdirprod.
  apply isapropisirrefl.
  apply isapropdirprod.
  apply isapropissymm.
  apply isapropiscotrans.
Qed.

Definition aprel (X : UU) := ∑ ap : hrel X, isaprel ap.
Definition aprel_pr1 {X : UU} (ap : aprel X) : hrel X := pr1 ap.
Coercion aprel_pr1 : aprel >-> hrel.

Definition apSet := ∑ X : hSet, aprel X.
Definition apSet_pr1 (X : apSet) : hSet := pr1 X.
Coercion apSet_pr1 : apSet >-> hSet.
Arguments apSet_pr1 X: simpl never.
Definition apSet_pr2 (X : apSet) : aprel X := pr2 X.
Notation "x # y" := (apSet_pr2 _ x y) : ap_scope.

Delimit Scope ap_scope with ap.
Open Scope ap_scope.

(** Lemmas about apartness *)

Lemma isirreflapSet {X : apSet} :
  ∏ x : X, ¬ (x # x).
Proof.
  intros ?.
  exact (pr1 (pr2 (pr2 X))).
Qed.

Lemma issymmapSet {X : apSet} :
  ∏ x y : X, x # y -> y # x.
Proof.
  intros ?.
  exact (pr1 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma iscotransapSet {X : apSet} :
  ∏ x y z : X, x # z -> x # y ∨ y # z.
Proof.
  intros ?.
  exact (pr2 (pr2 (pr2 (pr2 X)))).
Qed.
Close Scope ap_scope.

(** ** Tight apartness *)

Definition istight {X : UU} (R : hrel X) :=
  ∏ x y : X, ¬ (R x y) -> x = y.
Definition istightap {X : UU} (ap : hrel X) :=
  isaprel ap × istight ap.

Definition tightap (X : UU) := ∑ ap : hrel X, istightap ap.
Definition tightap_aprel {X : UU} (ap : tightap X) : aprel X := pr1 ap ,, (pr1 (pr2 ap)).
Coercion tightap_aprel : tightap >-> aprel.

Definition tightapSet := ∑ X : hSet, tightap X.
Definition tightapSet_apSet (X : tightapSet) : apSet := pr1 X ,, (tightap_aprel (pr2 X)).
Coercion tightapSet_apSet : tightapSet >-> apSet.

Definition tightapSet_rel (X : tightapSet) : hrel X := (pr1 (pr2 X)).
Notation "x ≠ y" := (tightapSet_rel _ x y) (at level 70, no associativity) : tap_scope.

Delimit Scope tap_scope with tap.
Open Scope tap_scope.

(** Some lemmas *)

Lemma isirrefltightapSet {X : tightapSet} :
  ∏ x : X, ¬ (x ≠ x).
Proof.
  intros ?.
  exact isirreflapSet.
Qed.

Lemma issymmtightapSet {X : tightapSet} :
  ∏ x y : X, x ≠ y -> y ≠ x.
Proof.
  intros ?.
  exact issymmapSet.
Qed.

Lemma iscotranstightapSet {X : tightapSet} :
  ∏ x y z : X, x ≠ z -> x ≠ y ∨ y ≠ z.
Proof.
  intros ?.
  exact iscotransapSet.
Qed.

Lemma istighttightapSet {X : tightapSet} :
  ∏ x y : X, ¬ (x ≠ y) -> x = y.
Proof.
  intros ?.
  exact (pr2 (pr2 (pr2 X))).
Qed.

Lemma istighttightapSet_rev {X : tightapSet} :
  ∏ x y : X, x = y -> ¬ (x ≠ y).
Proof.
  intros ? x _ <-.
  now apply isirrefltightapSet.
Qed.

Lemma tightapSet_dec {X : tightapSet} :
  LEM -> ∏ x y : X, (x != y <-> x ≠ y).
Proof.
  intros ? Hdec x y.
  destruct (Hdec (x ≠ y)) as [ Hneq | Heq ].
  - split.
    + intros _ ; apply Hneq.
    + intros _ Heq.
      rewrite <- Heq in Hneq.
      revert Hneq.
      now apply isirrefltightapSet.
  - split.
    + intros Hneq.
      apply fromempty, Hneq.
      now apply istighttightapSet.
    + intros Hneq.
      exact (fromempty (Heq Hneq)).
Qed.

(** ** Operations and apartness *)

Definition isapunop {X : tightapSet} (op :unop X) :=
  ∏ x y : X, op x ≠ op y -> x ≠ y.
Lemma isaprop_isapunop {X : tightapSet} (op :unop X) :
  isaprop (isapunop op).
Proof.
  intros ? ap op.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply isapropimpl.
  now apply pr2.
Qed.

Definition islapbinop {X : tightapSet} (op : binop X) :=
  ∏ x, isapunop (λ y, op y x).
Definition israpbinop {X : tightapSet} (op : binop X) :=
  ∏ x, isapunop (λ y, op x y).
Definition isapbinop {X : tightapSet} (op : binop X) :=
  (islapbinop op) × (israpbinop op).
Lemma isaprop_islapbinop {X : tightapSet} (op : binop X) :
  isaprop (islapbinop op).
Proof.
  intros ? op.
  apply impred_isaprop ; intro x.
  now apply isaprop_isapunop.
Qed.
Lemma isaprop_israpbinop {X : tightapSet} (op : binop X) :
  isaprop (israpbinop op).
Proof.
  intros ? op.
  apply impred_isaprop ; intro x.
  now apply isaprop_isapunop.
Qed.
Lemma isaprop_isapbinop {X : tightapSet} (op :binop X) :
  isaprop (isapbinop op).
Proof.
  intros ? ap op.
  apply isapropdirprod.
  now apply isaprop_islapbinop.
  now apply isaprop_israpbinop.
Qed.

Definition apbinop (X : tightapSet) := ∑ op : binop X, isapbinop op.
Definition apbinop_pr1 {X : tightapSet} (op : apbinop X) : binop X := pr1 op.
Coercion apbinop_pr1 : apbinop >-> binop.

Definition apsetwithbinop := ∑ X : tightapSet, apbinop X.
Definition apsetwithbinop_pr1 (X : apsetwithbinop) : tightapSet := pr1 X.
Coercion apsetwithbinop_pr1 : apsetwithbinop >-> tightapSet.
Definition apsetwithbinop_setwithbinop : apsetwithbinop -> setwithbinop :=
  λ X : apsetwithbinop, (apSet_pr1 (apsetwithbinop_pr1 X)),, (pr1 (pr2 X)).
Definition op {X : apsetwithbinop} : binop X := op (X := apsetwithbinop_setwithbinop X).

Definition apsetwith2binop := ∑ X : tightapSet, apbinop X × apbinop X.
Definition apsetwith2binop_pr1 (X : apsetwith2binop) : tightapSet := pr1 X.
Coercion apsetwith2binop_pr1 : apsetwith2binop >-> tightapSet.
Definition apsetwith2binop_setwith2binop : apsetwith2binop -> setwith2binop :=
  λ X : apsetwith2binop,
        apSet_pr1 (apsetwith2binop_pr1 X),, pr1 (pr1 (pr2 X)),, pr1 (pr2 (pr2 X)).
Definition op1 {X : apsetwith2binop} : binop X := op1 (X := apsetwith2binop_setwith2binop X).
Definition op2 {X : apsetwith2binop} : binop X := op2 (X := apsetwith2binop_setwith2binop X).

(** Lemmas about sets with binops *)

Section apsetwithbinop_pty.

Context {X : apsetwithbinop}.

Lemma islapbinop_op :
  ∏ x x' y : X, op x y ≠ op x' y -> x ≠ x'.
Proof.
  intros x y y'.
  now apply (pr1 (pr2 (pr2 X))).
Qed.

Lemma israpbinop_op :
  ∏ x y y' : X, op x y ≠ op x y' -> y ≠ y'.
Proof.
  intros x y y'.
  now apply (pr2 (pr2 (pr2 X))).
Qed.

Lemma isapbinop_op :
  ∏ x x' y y' : X, op x y ≠ op x' y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  intros x x' y y' Hop.
  apply (iscotranstightapSet _ (op x' y)) in Hop.
  revert Hop ; apply hinhfun ; intros [Hop | Hop].
  - left ; revert Hop.
    now apply islapbinop_op.
  - right ; revert Hop.
    now apply israpbinop_op.
Qed.

End apsetwithbinop_pty.

Section apsetwith2binop_pty.

Context {X : apsetwith2binop}.

Definition apsetwith2binop_apsetwithbinop1 : apsetwithbinop :=
  (pr1 X) ,, (pr1 (pr2 X)).
Definition apsetwith2binop_apsetwithbinop2 : apsetwithbinop :=
  (pr1 X) ,, (pr2 (pr2 X)).

Lemma islapbinop_op1 :
  ∏ x x' y : X, op1 x y ≠ op1 x' y -> x ≠ x'.
Proof.
  exact (islapbinop_op (X := apsetwith2binop_apsetwithbinop1)).
Qed.

Lemma israpbinop_op1 :
  ∏ x y y' : X, op1 x y ≠ op1 x y' -> y ≠ y'.
Proof.
  exact (israpbinop_op (X := apsetwith2binop_apsetwithbinop1)).
Qed.

Lemma isapbinop_op1 :
  ∏ x x' y y' : X, op1 x y ≠ op1 x' y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (isapbinop_op (X := apsetwith2binop_apsetwithbinop1)).
Qed.

Lemma islapbinop_op2 :
  ∏ x x' y : X, op2 x y ≠ op2 x' y -> x ≠ x'.
Proof.
  exact (islapbinop_op (X := apsetwith2binop_apsetwithbinop2)).
Qed.

Lemma israpbinop_op2 :
  ∏ x y y' : X, op2 x y ≠ op2 x y' -> y ≠ y'.
Proof.
  exact (israpbinop_op (X := apsetwith2binop_apsetwithbinop2)).
Qed.

Lemma isapbinop_op2 :
  ∏ x x' y y' : X, op2 x y ≠ op2 x' y' -> x ≠ x' ∨ y ≠ y'.
Proof.
  exact (isapbinop_op (X := apsetwith2binop_apsetwithbinop2)).
Qed.

End apsetwith2binop_pty.

Close Scope tap_scope.