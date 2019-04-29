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

  Definition nat_algebra2: Algebra nat_signature := mkalgebra natset nat_ops2.

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

  Goal status_cons nat_succ (statusok 1) = statusok 1.
  Proof. exact (idpath _). Qed.

  Goal status_cons nat_succ (statusok 0) = statuserror.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (statusok 1) (statusok 2) = statusok 3.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (statusok 1) statuserror = statuserror.
  Proof. exact (idpath _). Qed.

  Local Lemma one_status: list2status (nat_succ :: nat_zero :: nil) = statusok 1.
  Proof. exact (idpath _). Qed.

  Goal list2status(sigma:=nat_signature) nil = statusok 0.
  Proof. exact (idpath _). Qed.

  Local Definition term_zero: Stack nat_signature 1 :=
    mkstack (nat_zero :: nil) (idpath (statusok 1)).

  Local Definition term_one: Stack nat_signature 1 :=
    mkstack (nat_succ :: nat_zero :: nil) one_status.

  Goal list2status term_one = statusok 1.
  Proof. exact (idpath _). Qed.

  Local Definition term_two: Stack nat_signature 1 :=
    mkstack (nat_succ :: nat_succ :: nat_zero :: nil) one_status.

  Goal list2status term_two = statusok 1.
  Proof. exact (idpath _). Qed.

  Local Lemma zero_one_status: list2status (nat_zero :: nat_succ :: nat_zero :: nil) = statusok 2.
  Proof. exact (idpath _). Qed.

  Local Definition zero_one_stack: Stack nat_signature 2:=
    mkstack (nat_zero :: nat_succ :: nat_zero :: nil) zero_one_status.

  Goal list2status (nat_succ :: nil) = statuserror.
  Proof. exact (idpath _). Qed.

  Goal stack_concatenate term_zero term_one = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal terms2stack (term_zero ::: term_one ::: vnil) = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal mkterm nat_succ ((mkterm nat_zero vnil) ::: vnil) = term_one.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal princop term_two = nat_succ.
  Proof. exact (idpath _). Qed.

  Goal pr1 (extract_list zero_one_stack 0) = nil.
  Proof. exact (idpath _ ). Qed.

  Goal pr1 (extract_list zero_one_stack 0) = nil.
  Proof. exact (idpath _ ). Qed.

  Goal pr2 (extract_list zero_one_stack 0) = zero_one_stack.
  Proof. exact (idpath _). Qed.

  Goal pr1 (extract_list zero_one_stack 1) = term_zero.
  Proof. exact (idpath _). Qed.

  Goal stack_first zero_one_stack = term_zero.
  Proof. exact (idpath _). Qed.

  Goal el (subterms term_one) (●0) = term_zero.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal depth term_zero = 1.
  Proof. exact (idpath _). Qed.

  Goal depth term_one = 2.
  Proof. Abort.

End Nat.

Section Bool.
  Local Definition t_false: Term bool_signature := mkterm bool_false vnil.
  Local Definition t_true: Term bool_signature := mkterm bool_true vnil.
  Local Definition t1: Term bool_signature := mkterm bool_and (t_true ::: t_false ::: vnil).
  Local Definition t2: Term bool_signature := mkterm bool_not (t1 ::: vnil).

  Goal princop t1 = bool_and.
  Proof. exact (idpath _). Qed.

  Goal bool_not :: bool_and :: bool_true :: bool_false :: [] = t2.
  Proof. exact (idpath _). Qed.

  Goal pr1 (extract_list t1 0) = nil.
  Proof. exact (idpath _). Qed.

  Goal pr2 (extract_list t1 0) = t1.
  Proof. exact (idpath _). Qed.

  Goal pr1 (extract_list t1 1) = t1.
  Proof. exact (idpath _). Qed.

  Goal pr2 (extract_list t1 1) = nil.
  Proof. exact (idpath _). Qed.

  Goal el (subterms t2) (●0) = t1.
  Proof. exact (idpath _). Qed.

  Goal el (subterms t1) (●0) = t_true.
  Proof. exact (idpath _). Qed.

  Goal el (subterms t1) (●1) = t_false.
  Proof. exact (idpath _). Qed.

End Bool.
