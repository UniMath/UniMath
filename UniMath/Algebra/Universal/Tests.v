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

  Goal unithom nat_algebra 2 = tt.
  Proof. exact (idpath _). Qed.

  Goal Universal.statuscons nat_succ (Universal.statusok 1) = Universal.statusok 1.
  Proof. exact (idpath _). Qed.

  Goal Universal.statuscons nat_succ (Universal.statusok 0) = Universal.statuserror.
  Proof. exact (idpath _). Qed.

  Goal Universal.status_concatenate (Universal.statusok 1) (Universal.statusok 2) = Universal.statusok 3.
  Proof. exact (idpath _). Qed.

  Goal Universal.status_concatenate (Universal.statusok 1) Universal.statuserror = Universal.statuserror.
  Proof. exact (idpath _). Qed.

  Local Lemma one_status: Universal.oplist2status (nat_succ :: nat_zero :: nil) = Universal.statusok 1.
  Proof. exact (idpath _). Qed.

  Goal Universal.oplist2status(sigma:=nat_signature) nil = Universal.statusok 0.
  Proof. exact (idpath _). Qed.

  Eval cbn in pr1 ( Universal.oplist2vecoplist (nat_zero :: nat_succ :: nat_zero :: nil) (idpath (Universal.statusok 2)) ).

  Local Definition term_zero:= nat2term 0.

  Local Definition term_one:= nat2term 1.
  
  Local Definition term_two:= nat2term 2.
  
  Local Definition term_ten:= nat2term 10.

  Goal Universal.isaterm term_one.
  Proof. exact (idpath _). Qed.

  Goal Universal.isaterm term_two.
  Proof. exact (idpath _). Qed.

  Local Lemma zero_one_status: Universal.oplist2status (nat_zero :: nat_succ :: nat_zero :: nil) = Universal.statusok 2.
  Proof. exact (idpath _). Qed.

  (*
  Local Definition zero_one_stack: stack nat_signature 2:=
    make_stack (nat_zero :: nat_succ :: nat_zero :: nil) zero_one_status.
  *)

  Goal Universal.oplist2status (nat_succ :: nil) = Universal.statuserror.
  Proof. exact (idpath _). Qed.

  (*
  Goal stack_concatenate term_zero term_one = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.

  Goal terms2stack (term_zero ::: term_one ::: vnil) = zero_one_stack.
  Proof. apply stack_extens. exact (idpath _). Qed.
  *)

  Goal princop term_two = nat_succ.
  Proof. exact (idpath _). Qed.

  (**
  Goal stack_first zero_one_stack = term_zero.
  Proof. exact (idpath _). Qed.

  Goal stack2list (stack_rest zero_one_stack) = stack2list term_one.
  Proof. exact (idpath _). Qed.

  Goal vector_map stack2list (stack2terms zero_one_stack) = vector_map stack2list (term_zero ::: term_one ::: vnil).
  Proof. exact (idpath _). Qed.

  Goal pr1 (oplistsplit zero_one_stack 0) = nil.
  Proof. exact (idpath _ ). Qed.

  Goal pr1 (oplistsplit zero_one_stack 0) = nil.
  Proof. exact (idpath _ ). Qed.

  Goal pr2 (oplistsplit zero_one_stack 0) = zero_one_stack.
  Proof. exact (idpath _). Qed.

  Goal pr1 (oplistsplit zero_one_stack 1) = term_zero.
  Proof. exact (idpath _). Qed.

  Goal stack_first zero_one_stack = term_zero.
  Proof. exact (idpath _). Qed.

  **)

  Goal el (subterms term_one) (●0) = term_zero.
  Proof.  exact (idpath _). Qed.

  Goal el (subterms term_two) (●0) = term_one.
  Proof. exact (idpath _). Qed.
 
  Goal build_term (princop term_ten) (subterms term_ten) = nat2term 10.
  Proof. exact (idpath _). Qed.
 
  (* ----- oplist_decompose ----- *)

  (* slow but works *)
  (* Eval lazy in oplist_decompose term_ten (term2proof term_ten). *)

  Eval lazy in pr1 (oplist_decompose term_ten (term2proof term_ten)).
  
  Eval lazy in (pr1 (pr2 (oplist_decompose term_ten (term2proof term_ten)))).
  
  Eval lazy in (pr1 (pr2 (pr2 (oplist_decompose term_zero (term2proof term_zero) )))).

  (* long execution time *)
  (* Eval lazy in (pr1 (pr2 (pr2 (oplist_decompose term_ten (term2proof term_te) )))). *)
  
  Eval lazy in (pr2 (pr2 (pr2 (oplist_decompose term_zero (term2proof term_zero) )))).
  
  Eval lazy in (pr2 (pr2 (pr2 (oplist_decompose term_one (term2proof term_one) )))).
  
  (* long execution time *)
  (* Eval lazy in (pr2 (pr2 (pr2 (oplist_decompose term_ten (term2proof term_ten) )))). *)
   
  (* ----- term_decompose ----- *)
  
  (* does not terminate *)
  (* Eval lazy in term_decompose term_one. *)
  
  (* does not terminate. this is weird because we may evaluare all the 
     components separately *)
  (* Eval lazy in term_decompose term_zero. *)
  
  Eval lazy in pr1 (term_decompose term_ten).
  
  Eval lazy in (pr1 (pr2 (term_decompose term_ten))).
  
  Eval lazy in (pr1 (pr2 (pr2 (term_decompose term_zero)))).
  
  (* long execution time *)
  (* Eval lazy in (pr1 (pr2 (pr2 (term_decompose term_ten)))). *)
  
  Eval lazy in (pr2 (pr2 (pr2 (term_decompose term_zero)))).
  
  (* does not terminate *)
  (* Eval lazy in (pr2 (pr2 (pr2 (term_decompose term_one)))). *)
  
  (* ----- oplist_depth ------- *)

  Goal oplist_depth term_ten (term2proof term_ten) = 11.
  Proof. exact (idpath _). Qed.

  Eval lazy in (oplist_depth term_ten (pr2 term_ten)).
  
  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the induction *)
  (* Eval compute in (oplist_depth term_ten (pr2 term_ten)). *)

  (* ----- depth recursive ------- *)
  
  Goal depth_rec term_ten = 11.
  Proof. exact (idpath _). Qed.
  
  Eval lazy in depth_rec term_ten.
  
  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the recursion *)
  (* Eval compute in depth_rec term_ten. *)

  Goal depth_rec2 term_ten = 11.
  Proof. exact (idpath _). Qed.
  
  Eval lazy in depth_rec2 term_ten.
  
  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the recursion *)
  (* Eval compute in depth_rec2 term_ten. *)
  
  (* ----- depth inductive ------- *)
  
  Goal depth_ind term_zero = 1.
  Proof. exact (idpath _). Qed.
  
  (* does non terminate, even with lazy, due (?) to the transport required for induction *)
  (* Eval lazy in depth_ind term_one. *)
  
  (* does not work *)
  (*
    Goal depth_ind term_one = 2.
    Proof. exact (idpath _). Qed.
  *)

  Goal depth_ind2 term_zero = 1.
  Proof. exact (idpath _). Qed.
  
  (* does non terminate, even with lazy, due (?) to the transport required for induction *)
  (* Eval lazy in depth_ind2 term_one. *)
  
  (* does not work *)
  (*
    Goal depth_ind2 term_one = 2.
    Proof. exact (idpath _). Qed.
  *)
  
  Goal depth_ind3 term_zero = 1.
  Proof. exact (idpath _). Qed.
  
  (* does non terminate, even with lazy, due (?) to the transport required for induction *)
  (* Eval lazy in depth_ind3 term_one. *)
  
  (* does not work *)
  (*
    Goal depth_ind3 term_one = 2.
    Proof. exact (idpath _). Qed.
  *)

End Nat.

Section Bool.
  Local Definition t_false: term bool_signature := build_term bool_false vnil.
  Local Definition t_true: term bool_signature := build_term bool_true vnil.
  Local Definition t1: term bool_signature := build_term bool_and (t_true ::: t_false ::: vnil).
  Local Definition t2: term bool_signature := build_term bool_not (t1 ::: vnil).

  Goal princop t1 = bool_and.
  Proof. exact (idpath _). Qed.

  Goal bool_not :: bool_and :: bool_true :: bool_false :: [] = t2.
  Proof. exact (idpath _). Qed.

  Goal pr1 (Universal.oplistsplit t1 0) = nil.
  Proof. exact (idpath _). Qed.

  Goal pr2 (Universal.oplistsplit t1 0) = t1.
  Proof. exact (idpath _). Qed.

  Goal pr1 (Universal.oplistsplit t1 1) = t1.
  Proof. exact (idpath _). Qed.

  Goal pr2 (Universal.oplistsplit t1 1) = nil.
  Proof. exact (idpath _). Qed.

  Goal el (subterms t2) (●0) = t1.
  Proof. apply term_extens. exact (idpath _). Qed.

  Goal el (subterms t1) (●0) = t_true.
  Proof. exact (idpath _). Qed.

  Goal el (subterms t1) (●1) = t_false.
  Proof. apply term_extens. exact (idpath _). Qed.

  Eval lazy in oplist_depth t1 (term2proof t1).

  Eval lazy in oplist_depth t2 (term2proof t2).

End Bool.
