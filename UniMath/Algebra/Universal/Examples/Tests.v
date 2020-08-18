(** * Several tests for univeral algebra operations *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.DecSet.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.SortedTypes.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Terms.
Require Import UniMath.Algebra.Universal.TermAlgebras.
Require Import UniMath.Algebra.Universal.Examples.Nat.
Require Import UniMath.Algebra.Universal.Examples.Bool.

Local Open Scope stn.

Section SortedTypes.

Local Definition A : sUU bool := bool_ind _ nat unit.

Goal star A (cons true (cons false (cons true nil))) = (nat × unit × nat × unit).
Proof. apply idpath. Defined.

End SortedTypes.

Section NatLowLevel.

  Goal Terms.statuscons nat_succ_op (@Terms.statusok nat_signature [tt]) = @Terms.statusok nat_signature [tt].
  Proof. apply idpath. Qed.

  Goal Terms.statuscons nat_succ_op (@Terms.statusok nat_signature []) = Terms.statuserror.
  Proof. apply idpath. Qed.

  Goal Terms.statusconcatenate (@Terms.statusok nat_signature [tt]) (@Terms.statusok nat_signature [tt ; tt]) 
    = @Terms.statusok nat_signature [tt ; tt ; tt ].
  Proof. apply idpath. Qed.

  Goal Terms.statusconcatenate (@Terms.statusok nat_signature [tt]) Terms.statuserror = Terms.statuserror.
  Proof. apply idpath. Qed.

  Local Definition zero_one_oplist: Terms.oplist nat_signature := [nat_zero_op ; nat_succ_op ; nat_zero_op].

  Local Definition one_oplist: Terms.oplist nat_signature := [nat_succ_op ; nat_zero_op].

  Local Definition zero_oplist: Terms.oplist nat_signature := [nat_zero_op]%list.

  Goal @Terms.oplist2status nat_signature [] = Terms.statusok [].
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status one_oplist = @Terms.statusok nat_signature [tt].
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status zero_one_oplist = @Terms.statusok nat_signature [tt ; tt].
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status [nat_succ_op] = Terms.statuserror.
  Proof. apply idpath. Qed.

  Goal @Terms.isaterm nat_signature tt (nat2term 10).
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit zero_one_oplist 0) = nil.
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit zero_one_oplist 0) = zero_one_oplist.
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit zero_one_oplist 1) = zero_oplist.
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit zero_one_oplist 1) = one_oplist.
  Proof. apply idpath. Qed.

End NatLowLevel.

Section Nat.

  Local Definition term_zero := nat_zero.

  Local Definition term_one := nat_succ nat_zero.

  Local Definition term_two := nat_succ (nat_succ nat_zero).

  Local Definition term_four := nat_succ (nat_succ (nat_succ (nat_succ nat_zero))).

  (* ----- term_decompose ----- *)

  (* does not terminate *)
  (* Eval lazy in Terms.term_decompose term_one. *)

  (* does not terminate. this is weird because we may evaluare all the
     components separately *)
  (* Eval lazy in Terms.term_decompose term_zero. *)

  (* works, but long execution time *)
  (* Eval lazy in (pr1 (pr2 (pr2 (Terms.term_decompose term_ten)))). *)

  (* works *)
  (* Eval lazy in (pr2 (pr2 (pr2 (Terms.term_decompose term_zero)))). *)

  (* does not terminate *)
  (* Eval lazy in (pr2 (pr2 (pr2 (Terms.term_decompose term_one)))). *)

  Goal princop term_four = nat_succ_op.
  Proof. apply idpath. Qed.

  Goal subterms term_one = [term_zero]%hvec.
  Proof. apply idpath. Qed.

  Goal subterms term_two = [term_one]%hvec.
  Proof. apply idpath. Qed.

  Goal build_term (princop term_four) (subterms term_four) = term_four.
  Proof. apply idpath. Qed.

  (* FIX DOES NOT COMPUTE
    Goal depth term_four = 5.
    Proof. apply idpath. Qed.
  *)

  (* works *)
  (* Eval lazy in depth term_four. *)

  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the recursion *)
  (* Eval compute in depth term_four. *)
  
  (* FIX DOES NOT COMPUTE 
  Goal eval nat_algebra tt term_zero = 0.
  Proof. apply idpath. Qed.

  Goal eval nat_algebra tt term_one = 1.
  Proof. apply idpath. Qed.
  *)
  
  Goal nat2term 4 = term_four.
  Proof. apply idpath. Qed.

  (* FIX DOES NOT COMPUTE
  Goal eval nat_algebra tt (nat2term 4) = 4.
  Proof. apply idpath. Qed.
  *)

End Nat.

Section NatHom.

  Goal ∏ x: nat, (hom2fun (homid nat_algebra)) tt x = x.
  Proof. apply idpath. Qed.

  Local Definition nat_algebra2 := make_algebra_simple_single_sorted nat_signature natset [ λ _, 1 ;  λ x, S (pr1 x) ].

  Local Definition homnats: hom nat_algebra nat_algebra2.
  Proof.
    exists (λ (s: unit) (x: nat), S x).
    unfold ishom.
    intros.
    induction nm as [n proofn].
    induction n.
    { cbn. apply idpath. }
    induction n.
    { cbn. apply idpath.     }
    { exact (fromempty (nopathsfalsetotrue proofn)).  }
  Defined.

  Goal (hom2fun homnats) tt 2 = 3.
  Proof. apply idpath. Qed.

  Goal (hom2fun (homcomp (homid nat_algebra) homnats)) tt 2 = 3.
  Proof. apply idpath. Qed.

  Goal hom2fun (unithom nat_algebra) tt 2 = tt.
  Proof. apply idpath. Qed.

End NatHom.

Section Bool.

  Local Definition t_false := bool_false.
  Local Definition t_true := bool_true.
  Local Definition t1 := bool_and bool_true bool_false.
  Local Definition t2 := bool_not t1.

  Goal princop t1 = bool_and_op.
  Proof. apply idpath. Qed.

  Goal ([ bool_not_op ; bool_and_op ; bool_true_op ; bool_false_op ])%list = term2oplist t2.
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit (term2oplist t1) 0) =  []%list.
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit (term2oplist t1) 0) = (term2oplist t1).
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit (term2oplist t1) 1) = (term2oplist t1).
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit (term2oplist t1) 1) = []%list.
  Proof. apply idpath. Qed.

  Goal subterms t2 = [ t1 ]%hvec.
  Proof. apply idpath. Qed.

  Goal subterms t1 = [ t_true ; t_false ]%hvec.
  Proof. apply idpath. Qed.

  (* FIX 
  Goal depth t2 = 3.
  Proof. apply idpath. Qed.
  *)

  Definition simple_t := bool_not (bool_and (bool_or bool_true bool_false) (bool_not bool_false)).

  (* FIX DOES NOT COMUTE
  
  Lemma l1: eval bool_algebra tt bool_true = true.
  Proof. apply idpath. Defined.

  Lemma l2: eval bool_algebra tt (bool_not bool_true) = false.
  Proof. apply idpath. Defined.

  Lemma l3: eval bool_algebra tt (bool_and bool_true bool_false) = false.
  Proof. apply idpath. Defined.

  Lemma l4: eval bool_algebra tt simple_t = false.
  Proof. apply idpath. Defined.
*)

End Bool.
