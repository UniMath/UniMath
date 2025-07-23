(** ** Set Based Polynomial Functors

    Author : Ralph Matthes (@rmatthes), 2025

*)

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.

Local Open Scope cat.

Section SetBasedPolynomialFunctors.

  Context (A : hSet).
  Context (B : A -> hSet).

  Definition polynomial_functor_HSET_obj (X : hSet) : hSet.
  Proof.
    exists (polynomial_functor_obj (pr1hSet A) (fun a => pr1hSet (B a)) X).
    unfold polynomial_functor_obj.
    transparent assert (f : (pr1hSet A -> hSet)).
    { intro a.
      use tpair.
      - exact (pr1hSet (B a) -> pr1hSet X).
      - apply isaset_forall_hSet.
    }
    exact (isaset_total2_hSet _ f).
  Defined.

  Definition polynomial_functor_HSET_data : functor_data HSET HSET.
  Proof.
    use make_functor_data.
    - exact polynomial_functor_HSET_obj.
    - intros X Y.
      simpl.
      apply (polynomial_functor_arr (pr1hSet A) (fun a => pr1hSet (B a))).
  Defined.

  Lemma polynomial_functor_HSET_is_functor : is_functor polynomial_functor_HSET_data.
  Proof.
    split.
    - intro.
      apply idpath.
    - intros ? ? ? ? ?.
      apply idpath.
  Qed.

  Definition polynomial_functor_HSET : functor HSET HSET := _ ,, polynomial_functor_HSET_is_functor.

End SetBasedPolynomialFunctors.
