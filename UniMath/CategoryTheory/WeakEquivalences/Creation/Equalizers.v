Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
(* Require Import UniMath.CategoryTheory.Core.NaturalTransformations. *)

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Equalizers.

Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Equalizers.

Local Open Scope cat.

Definition weak_equiv_into_univ_creates_equalizers
    {C1 C2 : category}
    (C2_univ : is_univalent C2)
    {F : C1 ⟶ C2}
    (Fw : is_weak_equiv F)
    (E₁ : Equalizers C1)
    : Equalizers C2.
Proof.
  intros x' y' f' g'.

  assert (pEq : isaprop (Equalizer f' g')).
  { apply isaprop_Equalizer, C2_univ. }

  use (factor_through_squash pEq _ (eso_from_weak_equiv _ Fw x')).
  intros [x iₓ].
  use (factor_through_squash pEq _ (eso_from_weak_equiv _ Fw y')).
  intros [y iy].

  set (f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (iₓ · f' · pr12 iy)).
  set (g₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (iₓ · g' · pr12 iy)).

  set (E1_fg := E₁ _ _ f₁ g₁).
  set (t :=  weak_equiv_preserves_equalizers Fw _ _ _ _ _ _ _ (Equalizers.p_func (p := pr12 E1_fg)) (pr22 E1_fg)).
  set (tE := make_Equalizer _ _ _ _ t).

  apply (EqualizerOfIso f' g' iₓ (z_iso_inv iy)).
  unfold f₁, g₁ in tE.
  do 2 rewrite functor_on_fully_faithful_inv_hom in tE.
  exact tE.
Defined.

Definition weak_equiv_into_univ_creates_hasequalizers
    {C1 C2 : category}
    (C2_univ : is_univalent C2)
    {F : C1 ⟶ C2}
    (Fw : is_weak_equiv F)
    (E₁ : hasEqualizers (C := C1))
    : hasEqualizers (C := C2).
Proof.
  intros x' y' f' g'.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x')).
  { apply propproperty. }
  intros [x iₓ].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y')).
  { apply propproperty. }
  intros [y iy].

  set (f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (iₓ · f' · pr12 iy)).
  set (g₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (iₓ · g' · pr12 iy)).

  use (factor_through_squash _ _ (E₁ _ _ f₁ g₁)).
  { apply propproperty. }
  intro p.
  set (t :=  weak_equiv_preserves_equalizers Fw _ _ _ _ _ _ _ (Equalizers.p_func (p := pr12 p)) (pr22 p)).
  set (tE := make_Equalizer _ _ _ _ t).

  apply hinhpr.
  apply (EqualizerOfIso f' g' iₓ (z_iso_inv iy)).
  unfold f₁, g₁ in tE.
  do 2 rewrite functor_on_fully_faithful_inv_hom in tE.

  exact tE.
Defined.
