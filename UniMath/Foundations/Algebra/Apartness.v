(** * Definition of appartness relation *)
(** Catherine Lelay. Sep. 2015 *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

Require Export UniMath.Foundations.Algebra.BinaryOperations.

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

Definition aprel (X : UU) := Σ ap : hrel X, isaprel ap.
Definition aprel_pr1 {X : UU} (ap : aprel X) : hrel X := pr1 ap.
Coercion aprel_pr1 : aprel >-> hrel.

Definition apSet := Σ X : hSet, aprel X.
Definition apSet_pr1 (X : apSet) : hSet := pr1 X.
Coercion apSet_pr1 : apSet >-> hSet.
Notation "x # y" := (pr2 (_ : apSet) x y).

(** ** Operations and apartness *)

Definition isapunop {X : apSet} (op :unop X) :=
  forall x y : X, op x # op y -> x # y.
Lemma isaprop_isapunop {X : apSet} (op :unop X) :
  isaprop (isapunop op).
Proof.
  intros ? ap op.
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply isapropimpl.
  now apply pr2.
Qed.

Definition islapbinop {X : apSet} (op : binop X) :=
  forall x, isapunop (λ y, op y x).
Definition israpbinop {X : apSet} (op : binop X) :=
  forall x, isapunop (λ y, op x y).
Definition isapbinop {X : apSet} (op : binop X) :=
  (islapbinop op) × (israpbinop op).
Lemma isaprop_islapbinop {X : apSet} (op : binop X) :
  isaprop (islapbinop op).
Proof.
  intros ? op.
  apply impred_isaprop ; intro x.
  now apply isaprop_isapunop.
Qed.
Lemma isaprop_israpbinop {X : apSet} (op : binop X) :
  isaprop (israpbinop op).
Proof.
  intros ? op.
  apply impred_isaprop ; intro x.
  now apply isaprop_isapunop.
Qed.
Lemma isaprop_isapbinop {X : apSet} (op :binop X) :
  isaprop (isapbinop op).
Proof.
  intros ? ap op.
  apply isapropdirprod.
  now apply isaprop_islapbinop.
  now apply isaprop_israpbinop.
Qed.

Definition apbinop (X : apSet) := Σ op : binop X, isapbinop op.
Definition apbinop_pr1 {X : apSet} (op : apbinop X) : binop X := pr1 op.
Coercion apbinop_pr1 : apbinop >-> binop.

Definition apsetwithbinop := Σ X : apSet, apbinop X.
Definition apsetwithbinop_pr1 (X : apsetwithbinop) : apSet := pr1 X.
Definition apsetwithbinop_setwithbinop : apsetwithbinop -> setwithbinop :=
  λ X : apsetwithbinop, (apSet_pr1 (apsetwithbinop_pr1 X)),, (pr1 (pr2 X)).
Coercion apsetwithbinop_setwithbinop : apsetwithbinop >-> setwithbinop.

Definition apsetwith2binop := Σ X : apSet, apbinop X × apbinop X.
Definition apsetwith2binop_pr1 (X : apsetwith2binop) : apSet := pr1 X.
Definition apsetwith2binop_setwith2binop : apsetwith2binop -> setwith2binop :=
  λ X : apsetwith2binop,
        apSet_pr1 (apsetwith2binop_pr1 X),, pr1 (pr1 (pr2 X)),, pr1 (pr2 (pr2 X)).
Coercion apsetwith2binop_setwith2binop : apsetwith2binop >-> setwith2binop.