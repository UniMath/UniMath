(** In this file, we show how any monoid in the monoidal category of endofunctors is a monad  - here w.r.t. the
    elementary definition of that monoidal category

    the bicategorical variant is found in [MonadsAsMonoidsWhiskered]

    we also show the direction from monads to monoids

 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.


Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section FixACategory.

  Context {C : category}.

Section MonoidToMonad.

  Context (M : category_of_monoids_in_monoidal_cat (monendocat_monoidal C)).

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

Section MonadToMonoid.

  Context (M : Monad C).

  Definition monad_to_monoid_CAT_data : monoid_data (monendocat_monoidal C) (M : C ⟶ C)
    := μ M ,, η M.

  Lemma monad_to_monoid_CAT_laws :  monoid_laws (monendocat_monoidal C) monad_to_monoid_CAT_data.
  Proof.
    split3; apply (nat_trans_eq C); intro c; cbn.
    - apply Monad_law2.
    - apply Monad_law1.
    - rewrite id_left. apply pathsinv0, Monad_law3.
  Qed.

  Definition monad_to_monoid_CAT_disp : monoid (monendocat_monoidal C) (M : C ⟶ C)
    := monad_to_monoid_CAT_data,,monad_to_monoid_CAT_laws.

  Definition monad_to_monoid_CAT : category_of_monoids_in_monoidal_cat (monendocat_monoidal C)
    := _,,monad_to_monoid_CAT_disp.

End MonadToMonoid.

End FixACategory.
