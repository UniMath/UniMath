(** In this file, we show how any monoid in the monoidal category of endofunctors is a monad  - here w.r.t. the
    elementary definition of that monoidal category

    the bicategorical variant is found in [MonadsAsMonoidsWhiskered]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.


Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsWhiskeredMonoidalElementary.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section MonoidToMonad.

  Context {C : category}.
  Let ENDO_CAT := monendocat_monoidal C.
  Let MON := category_of_monoids_in_monoidal_cat ENDO_CAT.

  Context (M : MON).

  Let x := monoid_carrier _ M.
  Let η := monoid_unit _ M.
  Let μ := monoid_multiplication _ M.

  Definition monoid_to_monad_multiplication_CAT : functor_with_μ C.
  Proof.
    exists x.
    exact μ.
  Defined.

  Definition monoid_to_monad_data_CAT : Monad_data C.
  Proof.
    exists monoid_to_monad_multiplication_CAT.
    exact η.
  Defined.

  Lemma monoid_to_monoid_laws_CAT : Monad_laws monoid_to_monad_data_CAT.
  Proof.
    repeat split.
    - intro c.
      set (t := monoid_right_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_left_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_assoc_law _ M).
      refine (! (toforallpaths _ _ _ (base_paths _ _ t) c) @ _).
      etrans.
      1: apply assoc'.
      apply id_left.
  Qed.

  Definition monoid_to_monad_CAT : Monad C
    := _ ,, monoid_to_monoid_laws_CAT.

End MonoidToMonad.
