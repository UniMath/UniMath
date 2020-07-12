(** * Several tests for univeral algebra operations *)

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


Local Definition A : sortedhSet boolset := bool_ind _ nat unit.

Eval cbn in sortedhSet_list A (cons true (cons false (cons true nil))).



Section NatLowLevel.

  Goal Terms.statuscons nat_succ_op (Terms.statusok 1) = Terms.statusok 1.
  Proof. apply idpath. Qed.

  Goal Terms.statuscons nat_succ_op (Terms.statusok 0) = Terms.statuserror.
  Proof. apply idpath. Qed.

  Goal Terms.statusconcatenate (Terms.statusok 1) (Terms.statusok 2) = Terms.statusok 3.
  Proof. apply idpath. Qed.

  Goal Terms.statusconcatenate (Terms.statusok 1) Terms.statuserror = Terms.statuserror.
  Proof. apply idpath. Qed.

  Local Definition zero_one_oplist: Terms.oplist nat_signature
    := nat_zero_op :: nat_succ_op :: nat_zero_op :: [].

  Local Definition one_oplist: Terms.oplist nat_signature
    := nat_succ_op :: nat_zero_op :: [].

  Local Definition zero_oplist: Terms.oplist nat_signature
    := nat_zero_op :: [].

  Goal Terms.oplist2status (sigma:=nat_signature) [] = Terms.statusok 0.
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status one_oplist = Terms.statusok 1.
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status zero_one_oplist = Terms.statusok 2.
  Proof. apply idpath. Qed.

  Goal Terms.oplist2status (nat_succ_op :: []) = Terms.statuserror.
  Proof. apply idpath. Qed.

  Goal Terms.isaterm (nat2term 10).
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit zero_one_oplist 0) = [].
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

  Goal el (subterms term_one) (●0) = term_zero.
  Proof. apply idpath. Qed.

  Goal el (subterms term_two) (●0) = term_one.
  Proof. apply idpath. Qed.

  Goal build_term (princop term_four) (subterms term_four) = term_four.
  Proof. apply idpath. Qed.

  Goal depth term_four = 5.
  Proof. apply idpath. Qed.

  (* works *)
  (* Eval lazy in depth term_four. *)

  (* does not terminate: compute is call-by-value, hence it needs to compute
     all the proofs involved in the recursion *)
  (* Eval compute in depth term_four. *)

  Goal eval nat_algebra term_zero = 0.
  Proof. apply idpath. Qed.

  Goal eval nat_algebra term_one = 1.
  Proof. apply idpath. Qed.

  Goal nat2term 4 = term_four.
  Proof. apply idpath. Qed.

  Goal eval nat_algebra (nat2term 4) = 4.
  Proof. apply idpath. Qed.

End Nat.

Section NatHom.

  Goal ∏ x: nat, homid nat_algebra x = x.
  Proof. apply idpath. Qed.

  Local Definition nat_ops2 (nm : names nat_signature): Vector nat (arity nm) → nat.
  Proof.
    induction nm as [n proofn].
    induction n.
    { cbn. exact (λ _, 1). }
    induction n.
    { cbn. exact (λ x, S(pr1 x)). }
    { exact (fromempty (nopathsfalsetotrue proofn)). }
  Defined.

  Local Definition nat_algebra2: algebra nat_signature := make_algebra natset nat_ops2.

  Local Definition homnats: hom nat_algebra nat_algebra2.
  Proof.
    exists (λ x: nat, S x).
    unfold ishom.
    intros.
    induction nm as [n proofn].
    induction n.
    { cbn. apply idpath. }
    induction n.
    { cbn. apply idpath.     }
    { exact (fromempty (nopathsfalsetotrue proofn)).  }
  Defined.

  Goal homnats 2 = 3.
  Proof. apply idpath. Qed.

  Goal homcomp (homid nat_algebra) homnats 2 = 3.
  Proof. apply idpath. Qed.

  Goal unithom nat_algebra 2 = tt.
  Proof. apply idpath. Qed.

End NatHom.

Section Bool.

  Local Definition t_false := bool_false.
  Local Definition t_true := bool_true.
  Local Definition t1 := bool_and bool_true bool_false.
  Local Definition t2 := bool_not t1.

  Goal princop t1 = bool_and_op.
  Proof. apply idpath. Qed.

  Goal bool_not_op :: bool_and_op :: bool_true_op :: bool_false_op :: [] = t2.
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit t1 0) = [].
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit t1 0) = t1.
  Proof. apply idpath. Qed.

  Goal pr1 (Terms.oplistsplit t1 1) = t1.
  Proof. apply idpath. Qed.

  Goal pr2 (Terms.oplistsplit t1 1) = [].
  Proof. apply idpath. Qed.

  Goal el (subterms t2) (●0) = t1.
  Proof. apply term_extens. apply idpath. Qed.

  Goal el (subterms t1) (●0) = t_true.
  Proof. apply idpath. Qed.

  Goal el (subterms t1) (●1) = t_false.
  Proof. apply term_extens. apply idpath. Qed.

  Goal depth t2 = 3.
  Proof. apply idpath. Qed.

  Definition simple_t := bool_not (bool_and (bool_or bool_true bool_false) (bool_not bool_false)).

  Lemma l1: eval bool_algebra bool_true = true.
  Proof. apply idpath. Defined.

  Lemma l2: eval bool_algebra (bool_not bool_true) = false.
  Proof. apply idpath. Defined.

  Lemma l3: eval bool_algebra (bool_and bool_true bool_false) = false.
  Proof. apply idpath. Defined.

  Lemma l4: eval bool_algebra simple_t = false.
  Proof. apply idpath. Defined.

End Bool.
