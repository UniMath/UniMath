(**
Let V be a monoidal category,
Given a monoid object y in V,
we show how the "constant functor" V → V : x ↦ y is part of a strong monoidal functor.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Local Open Scope cat.

Import MonoidalNotations.

Section ConstantFunctor.

  Context (V : monoidal_cat).

  Context {x : V} (m : monoid V x).

  Definition constant_functor_fmonoidal_data
    : fmonoidal_data V V (constant_functor _ _ x).
  Proof.
    use tpair.
    - intros ? ?.
      apply m.
    - apply m.
  Defined.

  Lemma constant_functor_fmonoidal_laxlaws
    : fmonoidal_laxlaws constant_functor_fmonoidal_data.
  Proof.
    repeat split ; (intro ; intros ; rewrite id_right).
    - rewrite (bifunctor_leftid V).
      apply id_left.
    - rewrite (bifunctor_rightid V).
      apply id_left.
    - apply pathsinv0, (monoid_to_assoc_law V m).
    - apply (monoid_to_unit_left_law V m).
    - apply (monoid_to_unit_right_law V m).
  Qed.

  Definition constant_functor_fmonoidal_lax
    : fmonoidal_lax V V (constant_functor _ _ x).
  Proof.
    exists constant_functor_fmonoidal_data.
    exact constant_functor_fmonoidal_laxlaws.
  Defined.

  Context (comul_iso : is_z_isomorphism (monoid_data_multiplication _ m))
    (counit_iso : is_z_isomorphism (monoid_data_unit _ m)).
  Definition constant_functor_fmonoidal_strong
    : fmonoidal_stronglaws
          (fmonoidal_preservestensordata constant_functor_fmonoidal_lax)
          (fmonoidal_preservesunit constant_functor_fmonoidal_lax).
  Proof.
    split.
    - intro ; intro.
      apply comul_iso.
    - apply counit_iso.
  Defined.

  Definition constant_functor_fmonoidal
    : fmonoidal V V (constant_functor _ _ x).
  Proof.
    exists constant_functor_fmonoidal_lax.
    exact constant_functor_fmonoidal_strong.
  Defined.

  Definition constant_functor_is_symmetric
               (S : symmetric V)
               (m_is_comm : pr1 S x x · monoid_data_multiplication _ m
                            = monoid_data_multiplication _ m)
    : is_symmetric_monoidal_functor S S constant_functor_fmonoidal.
  Proof.
    intro ; intro.
    rewrite id_right.
    apply m_is_comm.
  Qed.

End ConstantFunctor.

Section UnitExample.

  Context (V : monoidal_cat).

  Definition constantly_unit_functor_fmonoidal
    : fmonoidal V V (constant_functor _ _ (I_{V})).
  Proof.
    use constant_functor_fmonoidal.
    - apply unit_monoid.
    - exact (pr2 (leftunitor_nat_z_iso V) (I_{V})).
    - apply identity_is_z_iso.
  Defined.

  Definition constantly_unit_functor_is_symmetric
    (S : symmetric V)
    : is_symmetric_monoidal_functor S S constantly_unit_functor_fmonoidal.
  Proof.
    use constant_functor_is_symmetric.
    cbn.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (sym_mon_braiding_id (V,,S)).
  Defined.

End UnitExample.
