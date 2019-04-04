(** ** Refinement of M-types

    M-types can be refined to satisfy the right definitional equalities.
    This idea is from Felix Rech's Bachelor's thesis.

    Author: Dominik Kirst (@dominik-kirst)

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.categories.Types.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.Uniqueness.

Section Refinement.

  Local Open Scope functions.
  Local Open Scope cat.

  Context (A : UU).
  Context (B : A → UU).
  Local Notation F := (polynomial_functor A B).

  Variable M0 : coalgebra F.
  Local Notation carrierM0 := (pr1 M0).
  Local Notation destrM0 := (pr2 M0).

  Variable finalM0 : is_final M0.
  Local Notation corecM0 C := (pr11 (finalM0 C)).

  (* Refinement of the final coalgebra to computable elements *)

  Definition carrierM := ∑ m0 : carrierM0, ∃ C c, corecM0 C c = m0.

  (* Definition of the corecursor *)

  Definition corecM (C : coalgebra F) (c : pr1 C) :
    carrierM.
  Proof.
    exists (corecM0 C c). apply hinhpr. exists C, c. reflexivity.
  Defined.

  (* Definition of a proposition we factor the computation through *)

  Definition P (m : carrierM) :=
    ∑ af : F carrierM, destrM0 (pr1 m) = # F pr1 af.

  Lemma P_isaprop m :
    isaprop (P m).
  Proof.
  Admitted.

  (* Now the destructor of M can be defined *)

  Definition destrM' (m : carrierM) : P m.
  Proof.
    destruct m as [m0 H]. apply (squash_to_prop H); try apply P_isaprop.
    intros [C[c <-]]. refine ((# F (corecM C) ∘ (pr2 C)) c,,_). cbn [pr1]. clear H.
    assert (H : is_coalgebra_homo F (corecM0 C)).
    - destruct finalM0 as [[G H] H']. apply H.
    - apply toforallpaths in H. symmetry. apply H.
  Defined.

  Definition destrM (m : carrierM) : F carrierM :=
    pr1 (destrM' m).

  (* The destructor satisfies the corecursion equation computationally *)

  Lemma corec_computation C c :
    destrM (corecM C c) = # F (corecM C) (pr2 C c).
  Proof.
    reflexivity.
  Qed.

  (* We pack both components into a coalgebra *)

  Definition M : coalgebra F :=
    (carrierM,,destrM).

  (* The two carriers are equal *)

  Lemma eq_corecM0 m0 :
    corecM0 M0 m0 = m0.
  Proof.
    destruct finalM0 as [[G H1] H2]. cbn.
    specialize (H2 (coalgebra_homo_id F M0)).
    change (pr1 (G,,H1) m0 = m0).
    pattern (G,,H1). rewrite <- H2. reflexivity.
  Qed.

  Definition injectM0 m0 :
    ∃ C c, corecM0 C c = m0.
  Proof.
    apply hinhpr. exists M0, m0. apply eq_corecM0.
  Defined.

  Lemma carriers_weq :
    carrierM ≃ carrierM0.
  Proof.
    apply (weq_iso pr1 (fun m0 => m0,,injectM0 m0)).
    - intros [m H]. cbn. apply maponpaths, ishinh_irrel.
    - intros x. cbn. reflexivity.
  Defined.

  Lemma carriers_eq :
    carrierM = carrierM0.
  Proof.
    apply weqtopaths, carriers_weq.
  Defined.

  (* M is final *)

  Lemma help_eq1 (m : carrierM0) (H : ∃ C c, corecM0 C c = m) :
    @paths carrierM (m,, injectM0 m) (m,, H).
  Proof.
    apply maponpaths, ishinh_irrel.
  Qed.

  Lemma finalM :
    is_final M.
  Proof.
    intros C. unshelve refine ((corecM C,,idpath _),,_).
    intros [h H]. assert (h = corecM C) as ->.
    - apply funextsec. intros c. unfold corecM. admit.
    - apply maponpaths.
  Abort.

  (* The two coalgebras are equal *)

  Lemma eq1 (m0 : carrierM0) :
    transportf (λ X, X → F X) carriers_eq destrM m0
    = transportf (λ X, F X) carriers_eq (destrM (transportf (λ X, X) (!carriers_eq) m0)).
  Proof.
    destruct carriers_eq. reflexivity.
  Qed.

  Lemma eq2 (m0 : carrierM0) :
    transportf (λ X, X) (!carriers_eq) m0 = (m0,,injectM0 m0).
  Proof.
    apply (transportf_pathsinv0' (idfun UU) carriers_eq).
    unfold carriers_eq. rewrite (weqpath_transport carriers_weq).
    reflexivity.
  Qed.

  Definition eq3' (a : A) (f : B a -> carrierM) :
    transportf (λ X, F X) carriers_eq (a,,f) = (a,,transportf (λ X, B a -> X) carriers_eq f).
  Proof.
    destruct carriers_eq. reflexivity.
  Qed.

  Lemma tpair_eta X (Y : X -> UU) :
    forall (p : ∑ x, Y x), p = (pr1 p,,pr2 p).
  Proof.
    intros []. reflexivity.
  Qed.

  Definition eq3_right' (m0 : carrierM0) :=
    @tpair _ (fun a => B a -> carrierM0) (pr1 (destrM0 m0))
           (fun b => pr1 (corecM M0 (pr2 (destrM0 m0) b))).


  Definition eq3 m0 :
    destrM0 m0 = # F pr1 ((pr2 M0 · # F (corecM M0)) m0).
  Proof.
    cbn.
    unfold eq3_right. pattern (destrM0 m0) at 1. rewrite tpair_eta. cbn.
    assert (pr2 (destrM0 m0) = λ b : B (pr1 (destrM0 m0)), (corecM0 M0) (pr2 (destrM0 m0) b)).
    - apply funextsec. intros b. rewrite eq_corecM0. reflexivity.
    - rewrite X. cbn.
  Abort.

  Lemma coalgebras_eq :
    M = M0.
  Proof.
    use total2_paths_f.
    - apply weqtopaths, carriers_weq.
    - apply funextfun. intros m0.
      rewrite eq1. rewrite eq2.

      destruct (destrM (m0,, injectM0 m0)) as [a f] eqn : H.
      replace (destrM0 m0) with (eq3_right m0).
      + admit.
      + unfold eq3_right. pattern (destrM0 m0) at 1. rewrite tpair_eta. cbn.
    assert (pr2 (destrM0 m0) = λ b : B (pr1 (destrM0 m0)), (corecM0 M0) (pr2 (destrM0 m0) b)).
    - apply funextsec. intros b. rewrite eq_corecM0. reflexivity.
    - rewrite X. cbn.

      rewrite eq3. rewrite eq4. rewrite tpair_eta.
      assert (H' : pr1 (destrM (m0,, injectM0 m0)) = pr1 (pr2 M0 m0)).
      + unfold destrM, destrM'. cbn. apply maponpaths.
  Admitted.

  Definition eq3 (a : A) (f : B a -> carrierM) :
    transportf (λ X, F X) carriers_eq (a,,f) = (a,,transportf (λ X, pr2 (F X)) carriers_eq f).
  Proof. induction p; reflexivity. Defined.

  (* Thus M is final *)

  Lemma finalM :
    is_final M.
  Proof.
    rewrite coalgebras_eq. apply finalM0.
  Qed.

End Refinement.
