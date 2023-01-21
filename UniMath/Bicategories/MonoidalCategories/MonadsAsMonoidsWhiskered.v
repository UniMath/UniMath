(** In this file, we show how any monoid in the monoidal category of endofunctors is a monad **)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section MonoidToMonad.

  Context {C : category}.
  Let ENDO := monoidal_of_endofunctors C.
  Let MON := category_of_monoids_in_monoidal_cat ENDO.

  Context (M : MON).

  Let x := monoid_carrier _ M.
  Let η := monoid_unit _ M.
  Let μ := monoid_multiplication _ M.

  Definition monoid_to_monad_multiplication : functor_with_μ C.
  Proof.
    exists x.
    exact μ.
  Defined.

  Definition monoid_to_monad_data : Monad_data C.
  Proof.
    exists monoid_to_monad_multiplication.
    exact η.
  Defined.

  Lemma monoid_to_monoid_laws : Monad_laws monoid_to_monad_data.
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

  Definition monoid_to_monad : Monad C
    := _ ,, monoid_to_monoid_laws.

End MonoidToMonad.
