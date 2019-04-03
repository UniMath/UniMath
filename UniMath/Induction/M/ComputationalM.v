(** ** Refinement of M-types

    M-types can be refined to satisfy the right definitional equalities.
    This idea is from Felix Rech's Bachelor's thesis.

    Author: Dominik Kirst (@dominik-kirst)

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.

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
  Variable finalM0 : is_final M0.
  Local Notation corecM0 C := (pr11 (finalM0 C)).

  (* Refinement of the final coalgebra to computable elements *)

  Definition carrierM := ∑ m : pr1 M0, ∃ C c, corecM0 C c = m.

  (* Definition of the corecursor *)

  Definition corecM (C : coalgebra F) (c : pr1 C) :
    carrierM.
  Proof.
    exists (corecM0 C c). apply hinhpr. exists C, c. reflexivity.
  Defined.

  (* Definition of a proposition we factor the computation through *)

  Definition P (m : carrierM) :=
    ∑ af : F carrierM, pr2 M0 (pr1 m) = # F pr1 af.

  Lemma P_isaprop m :
    isaprop (P m).
  Proof.
  Admitted.

  (* Now the destructor of M can be defined *)

  Definition destrM' (m : carrierM) : P m.
  Proof.
    destruct m as [m0 H]. apply (squash_to_prop H); try apply P_isaprop.
    intros [C[c <-]]. refine  ((# F (corecM C) ∘ (pr2 C)) c,,_). cbn [pr1]. clear H.
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

End Refinement.
