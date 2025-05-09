(**************************************************************************************************

  The Empty Presheaf

  The initial object in the category of presheaves the presheaf where every set is empty.

  Contents
  1. The empty presheaf [empty_presheaf]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.


(** * 1. The empty presheaf *)

Section EmptyPresheaf.

  Context (L : algebraic_theory).

  Definition empty_presheaf_data
    : presheaf_data L.
  Proof.
    use make_presheaf_data.
    - intro n.
      exact (make_hSet ∅ isasetempty).
    - intros m n f g.
      induction f.
  Defined.

  Lemma empty_is_presheaf
    : is_presheaf empty_presheaf_data.
  Proof.
    use make_is_presheaf;
      intros;
      apply fromempty;
      assumption.
  Qed.

  Definition empty_presheaf
    : presheaf L
    := make_presheaf
      empty_presheaf_data
      empty_is_presheaf.

End EmptyPresheaf.
