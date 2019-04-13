(***** Universal Algebra ******)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Nat.
Require Import UniMath.Algebra.Universal.Bool.

Local Notation "[]" := nil (at level 0, format "[]").
Local Infix "::" := cons.
Local Infix ":::" := vcons (at level 60, right associativity).

Section Nat.

  Goal list2status (nat_succ :: nat_zero :: nil) = stackok 1.
  Proof. exact (idpath _). Qed.

  Goal list2status(sigma := nat_signature) nil = stackok 0.
  Proof. exact (idpath _). Qed.

  Goal list2status (nat_zero :: nat_zero :: nil) = stackok 2.
  Proof. exact (idpath _). Qed.

  Goal list2status (nat_succ :: nil) = stackerror.
  Proof. exact (idpath _). Qed.

  Goal term2list (term_op nat_succ ((term_op nat_zero vnil) ::: vnil))
  = nat_succ :: nat_zero :: nil.
  Proof. exact (idpath _). Qed.

End Nat.

Section Bool.

  Local Definition t_false: Term bool_signature := term_op bool_false vnil.
  Local Definition t_true: Term bool_signature := term_op bool_true vnil.
  Local Definition t1: Term bool_signature := term_op bool_and (t_true ::: t_false ::: vnil).
  Local Definition t2: Term bool_signature := term_op bool_not (t1 ::: vnil).

  Goal princ_op t1 = bool_and.
  Proof. exact (idpath _). Qed.

  Goal bool_not :: bool_and :: bool_true :: bool_false :: [] = t2.
  Proof. exact (idpath _). Qed.

  Goal pr1 (extract_substack t1 0 (natleh0n 0)) = stack_empty.
  Proof. exact (idpath _). Qed.

  (** Why the following type-checks?
  Compute (pr1 (extract_substack t1 1 (natleh0n 0))).
  **)

  (** Too slow
  Compute (term2list (subterm t2 (●0))).
  **)

  (** does not hold
  Goal subterm t2 (●0) = t1.
  Proof. reflexivity. Qed.
  **)

End Bool.
