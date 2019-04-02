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

  (** Following the paper, we have [X ⇒ Y] = Hom(X, Y) *)
  Local Notation F := (polynomial_functor A B). (* can be coerced to a function *)
  Local Notation "F*" := (polynomial_functor_arr A B).
  Local Notation "X ⇒ Y" := (coalgebra_homo F X Y).

  Variable M0 : coalgebra (polynomial_functor A B).
  Variable HM0 : is_final M0.

  Definition carrier_M := ∑ m : pr1 M0, ∃ C c, pr1 (pr1 (HM0 C)) c = m.

  Definition coiter_M (C : coalgebra (polynomial_functor A B)) (c : pr1 C) :
    carrier_M.
  Proof.
    exists (pr1 (pr1 (HM0 C)) c). apply hinhpr. exists C, c. reflexivity.
  Qed.




End Refinement.
