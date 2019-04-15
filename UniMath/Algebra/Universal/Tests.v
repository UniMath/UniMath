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

  Goal op nat_algebra nat_zero vnil = 0.
  Proof. exact (idpath _). Qed.

  Goal op nat_algebra nat_succ (0 ::: vnil) = 1.
  Proof. exact (idpath _). Qed.

  Goal ∏ x: nat, hom_id nat_algebra x = x.
  Proof. apply idpath. Qed.

  Definition nat_ops2 (nm : names nat_signature): Vector nat (arity nm) → nat.
  Proof.
    induction nm as [n proofn].
    induction n.
    { cbn. exact (λ _, 1). }
    induction n.
    { cbn. exact (λ x, S(pr1 x)). }
    { exact (fromempty (nopathsfalsetotrue proofn)). }
  Defined.

  Definition nat_algebra2: Algebra nat_signature := mk_algebra natset nat_ops2.

  Definition homnats: hom nat_algebra nat_algebra2.
  Proof.
    exists (λ x: nat, S x).
    unfold is_hom.
    intros.
    induction nm as [n proofn].
    induction n.
    { cbn. exact (idpath _). }
    induction n.
    { cbn. exact (idpath _).     }
    { exact (fromempty (nopathsfalsetotrue proofn)).  }
  Defined.

  Goal homnats 2 = 3.
  Proof. exact (idpath _). Qed.

  Goal hom_comp (hom_id nat_algebra) homnats 2 = 3.
  Proof. exact (idpath _). Qed.

  Goal terminal_hom nat_algebra 2 = tt.
  Proof. exact (idpath _). Qed.

  Goal status_cons nat_succ (stackok 1) = stackok 1.
  Proof. exact (idpath _). Qed.

  Goal status_cons nat_succ (stackok 0) = stackerror.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (stackok 1) (stackok 2) = stackok 3.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (stackok 1) stackerror = stackerror.
  Proof. exact (idpath _). Qed.

  Local Lemma one_status: list2status (nat_succ :: nat_zero :: nil) = stackok 1.
  Proof. exact (idpath _). Qed.

  Goal list2status(sigma:=nat_signature) nil = stackok 0.
  Proof. exact (idpath _). Qed.

  Local Definition one_stack: Stack nat_signature 1 :=
    mk_stack 1 (nat_succ :: nat_zero :: nil) one_status.

  Goal list2status one_stack = stackok 1.
  Proof. exact (idpath _). Qed.

  Local Definition two_stack: Stack nat_signature 1 :=
    mk_stack 1 (nat_succ :: nat_succ :: nat_zero :: nil) one_status.

  Goal list2status two_stack = stackok 1.
  Proof. exact (idpath _). Qed.

  Local Lemma double_zero_status: list2status (nat_zero :: nat_zero :: nil) = stackok 2.
  Proof. exact (idpath _). Qed.

  Local Definition double_zero_stack: Stack nat_signature 2:=
    mk_stack 2 (nat_zero :: nat_zero :: nil) double_zero_status.

  Goal list2status (nat_succ :: nil) = stackerror.
  Proof. exact (idpath _). Qed.

  Goal stack2list (stack_cons nat_succ one_stack (natleh0n 0)) = nat_succ :: nat_succ :: nat_zero :: nil.
  Proof. exact (idpath _). Qed.

  Goal stack2list (stack_concatenate one_stack double_zero_stack) = nat_succ :: nat_zero :: nat_zero :: nat_zero :: nil.
  Proof. exact (idpath _). Qed.

  Goal stack2list (stack_vector_concatenate (one_stack ::: two_stack ::: vnil)) = nat_succ :: nat_zero :: nat_succ :: nat_succ :: nat_zero :: nil.
  Proof. exact (idpath _). Qed.

  Goal term2list (term_op nat_succ ((term_op nat_zero vnil) ::: vnil)) = nat_succ :: nat_zero :: nil.
  Proof. exact (idpath _). Qed.

  Goal princ_op two_stack = nat_succ.
  Proof. exact (idpath _). Qed.

  (* Eval compute in stack2list (subterm one_stack  (●0)). *)
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

  Goal pr1 (extract_substack t1 0 (natleh0n 0)) = stack_empty bool_signature.
  Proof. exact (idpath _). Qed.

  Goal pr1 ( pr2 (extract_substack t1 0 (natleh0n 0))) = t1.
  Proof. exact (idpath _). Qed.

  Compute pr2 (pr2 (extract_substack t1 0 (natleh0n 0))).

  (* Compute hangs *)
  Eval cbn in stack2proof (pr1 (pr2 (extract_substack t1 0 (natleh0n 0)))).

  Eval cbn in stack2list (pr1 (extract_substack t1 1 (natleh0n 0))).

  Eval cbn in term2list (subterm t2 (●0)).

  Goal subterm t2 (●0) = t1.
  Proof. Abort.

End Bool.
