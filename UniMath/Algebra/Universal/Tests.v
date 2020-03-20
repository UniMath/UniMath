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

  Goal ∏ x: nat, homid nat_algebra x = x.
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

  Definition nat_algebra2: algebra nat_signature := make_algebra natset nat_ops2.

  Definition homnats: hom nat_algebra nat_algebra2.
  Proof.
    exists (λ x: nat, S x).
    unfold ishom.
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

  Goal homcomp (homid nat_algebra) homnats 2 = 3.
  Proof. exact (idpath _). Qed.

  Goal homtounit nat_algebra 2 = tt.
  Proof. exact (idpath _). Qed.

  Goal status_cons nat_succ (statusok 1) = statusok 1.
  Proof. exact (idpath _). Qed.

  Goal status_cons nat_succ (statusok 0) = statuserror.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (statusok 1) (statusok 2) = statusok 3.
  Proof. exact (idpath _). Qed.

  Goal status_concatenate (statusok 1) statuserror = statuserror.
  Proof. exact (idpath _). Qed.

  Local Lemma one_status: oplist2status (nat_succ :: nat_zero :: nil) = statusok 1.
  Proof. exact (idpath _). Qed.

  Goal oplist2status(sigma:=nat_signature) nil = statusok 0.
  Proof. exact (idpath _). Qed.

  Eval cbn in pr1 ( oplist2vecoplist (nat_zero :: nat_succ :: nat_zero :: nil) (idpath (statusok 2)) ).

  Local Definition term_zero: term nat_signature :=
    make_stack (nat_zero :: nil) (idpath (statusok 1)).

  Local Definition term_one: term nat_signature :=
    make_stack (nat_succ :: nat_zero :: nil) one_status.

  Goal oplist2status term_one = statusok 1.
  Proof. exact (idpath _). Qed.

  Local Definition term_two: term nat_signature :=
    make_stack (nat_succ :: nat_succ :: nat_zero :: nil) one_status.

  Goal oplist2status term_two = statusok 1.
  Proof. exact (idpath _). Qed.

  Local Lemma zero_one_status: oplist2status (nat_zero :: nat_succ :: nat_zero :: nil) = statusok 2.
  Proof. exact (idpath _). Qed.

  Local Definition zero_one_stack: stack nat_signature 2:=
    make_stack (nat_zero :: nat_succ :: nat_zero :: nil) zero_one_status.

  Goal oplist2status (nat_succ :: nil) = statuserror.
  Proof. exact (idpath _). Qed.

  Goal stack_concatenate term_zero term_one = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal terms2stack (term_zero ::: term_one ::: vnil) = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal make_term nat_succ ((make_term nat_zero vnil) ::: vnil) = term_one.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal princop term_two = nat_succ.
  Proof. exact (idpath _). Qed.

  Goal stack_first zero_one_stack = term_zero.
  Proof. exact (idpath _). Qed.

  Goal stack2list (stack_rest zero_one_stack) = stack2list term_one.
  Proof. exact (idpath _). Qed.

  (** In the following, the vector_map is needed because proofs cannot be unified **)

  Goal vector_map stack2list (stack2terms zero_one_stack) = vector_map stack2list (term_zero ::: term_one ::: vnil).
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

  Goal el (subterms term_two) (●0) = term_one.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal depth term_zero = 1.
  Proof. exact (idpath _). Qed.
  

  Goal pr1 (make_term (princop term_one) (subterms term_one)) = pr1 term_one.
  Proof. exact (idpath _). Qed.

  Goal oplist_depth term_one (pr2 term_one) = 2.
  Proof. exact (idpath _). Qed.

  Goal depth term_one = 2.
  Proof. Abort.

 End Nat.

Section Bool.
  Local Definition t_false: term bool_signature := make_term bool_false vnil.
  Local Definition t_true: term bool_signature := make_term bool_true vnil.
  Local Definition t1: term bool_signature := make_term bool_and (t_true ::: t_false ::: vnil).
  Local Definition t2: term bool_signature := make_term bool_not (t1 ::: vnil).

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

  Eval lazy in oplist_depth t1 (pr2 t1).

  Eval lazy in oplist_depth t2 (pr2 t2).

End Bool.
