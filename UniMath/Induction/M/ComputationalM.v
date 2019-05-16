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
Require Import UniMath.CategoryTheory.categories.Type.Core.

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
  Local Notation carrierM0 := (coalgebra_ob _  M0).
  Local Notation destrM0 := (coalgebra_mor _ M0).

  Variable finalM0 : is_final M0.
  Local Notation corecM0 C := (pr11 (finalM0 C)).

  (* Refinement of the final coalgebra to computable elements *)

  Definition carrierM := ∑ m0 : carrierM0, ∃ C c, corecM0 C c = m0.

  (* Definition of the corecursor *)

  Definition corecM (C : coalgebra F) (c : coalgebra_ob _ C) :
    carrierM.
  Proof.
    exists (corecM0 C c). apply hinhpr. exists C, c. apply idpath.
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
    intros [C[c <-]]. refine ((# F (corecM C) ∘ (pr2 C)) c,, _). cbn [pr1]. clear H.
    assert (H : is_coalgebra_homo F (corecM0 C)).
    - destruct finalM0 as [[G H] H']. apply H.
    - apply toforallpaths in H. symmetry. apply H.
  Defined.

  Definition destrM (m : carrierM) : F carrierM :=
    pr1 (destrM' m).

  Definition M : coalgebra F :=
    (carrierM,,destrM).

  (* The destructor satisfies the corecursion equation definitionally *)

  Lemma corec_computation C c :
    destrM (corecM C c) = # F (corecM C) (pr2 C c).
  Proof.
    apply idpath.
  Qed.

  (* The two carriers are equal *)

  Lemma eq_corecM0 m0 :
    corecM0 M0 m0 = m0.
  Proof.
    destruct finalM0 as [[G H1] H2]. cbn.
    specialize (H2 (coalgebra_homo_id F M0)).
    change (pr1 (G,, H1) m0 = m0).
    pattern (G,, H1). rewrite <- H2. apply idpath.
  Defined.

  Definition injectM0 m0 :
    ∃ C c, corecM0 C c = m0.
  Proof.
    apply hinhpr. exists M0, m0. apply eq_corecM0.
  Defined.

  Lemma carriers_weq :
    carrierM ≃ carrierM0.
  Proof.
    apply (weq_iso pr1 (λ m0, m0,, injectM0 m0)).
    - intros [m H]. cbn. apply maponpaths, ishinh_irrel.
    - intros x. cbn. apply idpath.
  Defined.

  Lemma carriers_eq :
    carrierM = carrierM0.
  Proof.
    apply weqtopaths, carriers_weq.
  Defined.

  (* The two coalgebras are equal *)

  Lemma tpair_eta X (Y : X -> UU) :
    forall (p : ∑ x, Y x), p = (pr1 p,,pr2 p).
  Proof.
    intros p. apply idpath.
  Qed.

  Definition transportf_sec_constant X Y (Z : X -> Y -> UU) x1 x2 (p : x1 = x2) f y :
    transportf (λ x, forall y, Z x y) p f y = transportf (λ x, Z x y) p (f y).
  Proof.
    destruct p. apply idpath.
  Defined.

  Definition transportf_total2_const X Y (Z : X -> Y -> UU) x y1 y2 (p : y1 = y2) z :
    transportf (λ y, ∑ a, Z a y) p (x,, z) = x,, transportf (Z x) p z.
  Proof.
    destruct p. apply idpath.
  Defined.

  Lemma eq1 (m0 : carrierM0) :
    transportf (λ X, X → F X) carriers_eq destrM m0
    = transportf (λ X, F X) carriers_eq (destrM (transportf (λ X, X) (!carriers_eq) m0)).
  Proof.
    destruct carriers_eq. apply idpath.
  Qed.

  Lemma eq2 (m0 : carrierM0) :
    transportf (λ X, X) (!carriers_eq) m0 = (m0,,injectM0 m0).
  Proof.
    apply (transportf_pathsinv0' (idfun UU) carriers_eq).
    unfold carriers_eq. rewrite weqpath_transport. apply idpath.
  Qed.

  (* this should hold (by computation) once P_isaprop was proven *)

  Lemma eq3 m0 :
    destrM (m0,, injectM0 m0) = pr1 (destrM0 m0),, (corecM M0 ∘ pr2 (destrM0 m0))%functions.
  Proof.
    cbn. unfold destrM, destrM'.
  Admitted.

  Lemma coalgebras_eq :
    M = M0.
  Proof.
    use total2_paths_f; try apply carriers_eq.
    apply funextfun. intros m0.
    rewrite eq1. rewrite eq2. rewrite eq3.
    cbn. unfold polynomial_functor_obj.
    rewrite transportf_total2_const.
    rewrite tpair_eta. use total2_paths_f; try apply idpath.
    cbn. apply funextsec. intros b. rewrite transportf_sec_constant.
    unfold carriers_eq. rewrite weqpath_transport.
    cbn. rewrite eq_corecM0. apply idpath.
  Qed.

  (* Thus M is final *)

  Lemma finalM :
    is_final M.
  Proof.
    rewrite coalgebras_eq. apply finalM0.
  Qed.

End Refinement.
