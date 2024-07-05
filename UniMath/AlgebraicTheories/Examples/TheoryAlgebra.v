(**************************************************************************************************

  The Theory Algebra

  For any algebraic theory T and any n, we can give the set T_n a T-algebra structure. This turns
    out to be the free T-algebra on n generators.

  Contents
  1. The T-algebra structure [theory_algebra]
  2. It is the free algebra on n generators [theory_algebra_free]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope algebraic_theories.

Section TheoryAlgebra.

  Context (T : algebraic_theory).
  Context (n : nat).


(** * 1. The T-algebra structure *)

  Definition theory_algebra_data
    : algebra_data T
    := make_algebra_data
      (T n)
      (λ _ f a, f • a).

  Lemma theory_is_algebra
    : is_algebra theory_algebra_data.
  Proof.
    use make_is_algebra.
    - intros.
      apply subst_subst.
    - intros.
      apply var_subst.
  Qed.

  Definition theory_algebra
    : algebra T
    := make_algebra _ theory_is_algebra.


(** * 2. It is the free algebra on n generators *)

  Section Free.

    Context (A : algebra T).

    Definition theory_algebra_free_mor
      (a : stn n → A)
      : algebra_morphism theory_algebra A.
    Proof.
      use make_algebra_morphism.
      - intro f.
        exact (action f a).
      - abstract (do 3 intro; apply subst_action).
    Defined.

    Definition theory_algebra_free_inv
      (F : algebra_morphism theory_algebra A)
      : stn n → A
      := λ i, F (var i).

    Lemma theory_algebra_free_inv_after_mor
      (a : stn n → A)
      : theory_algebra_free_inv (theory_algebra_free_mor a) = a.
    Proof.
      apply funextfun.
      intro.
      apply var_action.
    Qed.

    Lemma theory_algebra_free_mor_after_inv
      (F : algebra_morphism theory_algebra A)
      : theory_algebra_free_mor (theory_algebra_free_inv F) = F.
    Proof.
      apply algebra_morphism_eq.
      apply funextfun.
      intro f.
      refine (!mor_action _ _ _ @ _).
      apply maponpaths.
      apply subst_var.
    Qed.

    Definition theory_algebra_free
      : weq (stn n → A) (algebra_morphism theory_algebra A)
      := weq_iso
        theory_algebra_free_mor
        theory_algebra_free_inv
        theory_algebra_free_inv_after_mor
        theory_algebra_free_mor_after_inv.

  End Free.

End TheoryAlgebra.
