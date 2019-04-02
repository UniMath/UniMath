(** ** Refinement of M-types

    M-types can be refined to satisfy the right definitional equalities.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.Induction.All.

Section Refinement.

  Local Open Scope functions.
  Local Open Scope cat.

  Context (A : UU).
  Context (B : A → UU).
  Local Notation F := (polynomial_functor A B).

  Variable M0 : coalgebra F.
  Variable HM0 : is_final M0.

  Definition M_carrier := ∑ m : pr1 M0, ∃ C c, pr1 (pr1 (HM0 C)) c = m.

  Definition M_corec (C : coalgebra F) (c : pr1 C) :
    M_carrier.
  Proof.
    exists (pr1 (pr1 (HM0 C)) c). apply hinhpr. exists C, c. reflexivity.
  Defined.

  Definition P_help (af : F M_carrier) :
    F (pr1 M0).
  Proof.
    refine (pr1 af,,_).
    refine (fun x => pr1 (pr2 af x)).
  Defined.

  Definition P (m : M_carrier) :=
    ∑ af : F M_carrier, pr2 M0 (pr1 m) = P_help af.

  Lemma P_isaprop m :
    isaprop (P m).
  Proof.
  Admitted.

  Definition rec' (C : coalgebra F) (c : pr1 C) :
    F (pr1 M0).
  Proof.
    refine (pr1 (pr2 C c),,_).
    refine (fun x => pr11 (HM0 C) (pr2 (pr2 C c) x)).
  Defined.

  Lemma help C c :
    pr2 M0 ((pr11 (HM0 C)) c) = rec' C c.
  Proof.
  Admitted.

  Definition rec (C : coalgebra F) (c : pr1 C) :
    F M_carrier.
  Proof.
    refine (pr1 (pr2 C c),,_).
    refine (fun x => M_corec C (pr2 (pr2 C c) x)).
  Defined.

  Definition M_destr' (m : M_carrier) : P m.
  Proof.
    destruct m as [m0 H]. apply (squash_to_prop H); try apply P_isaprop.
    intros [C[c <-]]. refine  (rec C c,,_). unfold rec, P_help. cbn.
    apply help.
  Defined.

  Definition M_destr (m : M_carrier) : F M_carrier :=
    pr1 (M_destr' m).

  Lemma corec_computation C c :
    M_destr (M_corec C c) = rec C c.
  Proof.
    reflexivity.
  Qed.

End Refinement.
