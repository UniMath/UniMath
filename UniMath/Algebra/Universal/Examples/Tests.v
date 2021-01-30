(** * Several tests for univeral algebra operations. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.TermAlgebras.
Require Import UniMath.Algebra.Universal.Examples.Nat.
Require Import UniMath.Algebra.Universal.Examples.Bool.

Local Open Scope stn.
Local Open Scope sorted.
Local Open Scope hvec.
Local Open Scope list.

Section SortedTypes.

  Local Definition A : sUU bool := bool_ind _ nat unit.

  Goal A⋆ (cons true (cons false (cons true nil))) = (nat × unit × nat × unit).
  Proof. apply idpath. Defined.

End SortedTypes.

Section NatLowLevel.

  Goal Terms.opexec nat_succ_op (just [nat_sort]) = just [nat_sort].
  Proof. apply idpath. Qed.

  Goal Terms.opexec nat_succ_op (just []) = nothing.
  Proof. apply idpath. Qed.

  Local Definition zero_one_oplist: Terms.oplist nat_signature := [nat_zero_op ; nat_succ_op ; nat_zero_op].

  Local Definition one_oplist: Terms.oplist nat_signature := [nat_succ_op ; nat_zero_op].

  Local Definition zero_oplist: Terms.oplist nat_signature := [nat_zero_op].

  Goal @Terms.oplistexec nat_signature [] = just [].
  Proof. apply idpath. Qed.

  Goal Terms.oplistexec one_oplist = just [nat_sort].
  Proof. apply idpath. Qed.

  Goal Terms.oplistexec zero_one_oplist = just [nat_sort ; nat_sort].
  Proof. apply idpath. Qed.

  Goal Terms.oplistexec [nat_succ_op] = nothing.
  Proof. apply idpath. Qed.

  Goal Terms.isaterm nat_sort (nat2term 10).
  Proof. apply idpath. Qed.

  Goal Terms.stackconcatenate (just [nat_sort]) (just [nat_sort ; nat_sort])
    = just [nat_sort ; nat_sort ; nat_sort].
  Proof. apply idpath. Qed.

  Local Definition one_term : gterm nat_signature nat_sort := make_term(l:=one_oplist) (idpath _).

  Local Definition zero_term : gterm nat_signature nat_sort := make_term(l:=zero_oplist) (idpath _).

  Goal Terms.oplistsplit zero_one_oplist 0 = nil ,, zero_one_oplist.
  Proof. apply idpath. Qed.

  Goal Terms.oplistsplit zero_one_oplist 1 = zero_oplist ,, one_oplist.
  Proof. apply idpath. Qed.

  Goal Terms.vecoplist2oplist [zero_oplist; one_oplist] = zero_one_oplist.
  Proof. apply idpath. Qed.

  Goal h1map_vector (λ _, term2oplist) (pr1 (Terms.oplist2vecoplist zero_one_oplist (idpath _))) = vcons zero_oplist (vcons one_oplist vnil).
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplist2vecoplist zero_one_oplist (idpath _)) = vcons zero_term (vcons one_term vnil).
  Proof. apply idpath. Qed.

  Goal Terms.oplist_build nat_succ_op [zero_oplist] = one_oplist.
  Proof. apply idpath. Qed.

End NatLowLevel.

Section Nat.

  Local Definition term_zero := nat_zero.

  Local Definition term_one := nat_succ nat_zero.

  Local Definition term_two := nat_succ (nat_succ nat_zero).

  Local Definition term_four := nat_succ (nat_succ (nat_succ (nat_succ nat_zero))).

  Goal nat2term 4 = term_four.
  Proof. apply idpath. Qed.

  (* ----- term_decompose ----- *)

  (* works but slow, faster with lazy *)
  (* Eval compute in Terms.term_decompose term_one. *)

  Goal princop term_four = nat_succ_op.
  Proof. apply idpath. Qed.

  Goal subterms term_one = [( term_zero )].
  Proof. apply idpath. Qed.

  Goal subterms term_two = [( term_one )] .
  Proof. apply idpath. Qed.

  Goal build_gterm (princop term_four) (subterms term_four) = term_four.
  Proof. apply idpath. Qed.

  Goal depth term_four = 5.
  Proof. apply idpath. Qed.

  (* works *)
  (* Eval lazy in depth term_four. *)

  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the recursion *)
  (* Eval compute in depth term_four. *)

  Goal geval nat_algebra tt term_zero = 0.
  Proof. apply idpath. Qed.

  Goal geval nat_algebra tt term_one = 1.
  Proof. apply idpath. Qed.

  Goal geval nat_algebra tt (nat2term 4) = 4.
  Proof. apply idpath. Qed.

End Nat.

Section NatHom.

  Goal ∏ x: nat, homid nat_algebra tt x = x.
  Proof. apply idpath. Qed.

  Local Definition nat_algebra2
    := make_algebra_simple_single_sorted nat_signature natset [( λ _, 1 ;  λ x, S (pr1 x) )].

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

  Goal homnats nat_sort 2 = 3.
  Proof. apply idpath. Qed.

  Goal homcomp (homid nat_algebra) homnats nat_sort 2 = 3.
  Proof. apply idpath. Qed.

  Goal unithom nat_algebra nat_sort 2 = tt.
  Proof. apply idpath. Qed.

End NatHom.

Section Bool.
  Import UniMath.Algebra.Universal.Examples.Bool.GTerm.
  Local Open Scope stn.

  Local Definition bot_op  : names bool_signature := ●0.
  Local Definition top_op  : names bool_signature := ●1.
  Local Definition neg_op  : names bool_signature := ●2.
  Local Definition conj_op : names bool_signature := ●3.
  Local Definition disj_op : names bool_signature := ●4.
  Local Definition impl_op : names bool_signature := ●5.

  Local Definition t1 := conj top bot.
  Local Definition t2 := neg t1.

  Goal princop t1 = conj_op.
  Proof. apply idpath. Qed.

  Goal term2oplist t2 = [ neg_op ; conj_op ; top_op ; bot_op ].
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit (term2oplist t1) 0) =  [].
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit (term2oplist t1) 0) = (term2oplist t1).
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit (term2oplist t1) 1) = (term2oplist t1).
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit (term2oplist t1) 1) = [].
  Proof. apply idpath. Qed.

  Goal subterms t2 = [( t1 )].
  Proof. apply idpath. Qed.

  Goal subterms t1 = [( top ; bot )].
  Proof. apply idpath. Qed.

  Goal depth t2 = 3.
  Proof. apply idpath. Qed.

  Definition simple_t := neg (conj (disj top bot) (neg bot)).

  Local Lemma l1: geval bool_algebra tt top = true.
  Proof. apply idpath. Defined.

  Local Lemma l2: geval bool_algebra tt (neg top) = false.
  Proof. apply idpath. Defined.

  Local Lemma l3: geval bool_algebra tt (conj top bot) = false.
  Proof. apply idpath. Defined.

  Local Lemma l4: geval bool_algebra tt simple_t = false.
  Proof. apply idpath. Defined.

End Bool.
