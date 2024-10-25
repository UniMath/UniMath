Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
(* Require Import UniMath.CategoryTheory.Core.NaturalTransformations. *)

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.

Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.

Local Open Scope cat.

Lemma weak_equiv_into_univ_creates_pullbacks
  {C1 C2 : category}
  (C2_univ : is_univalent C2)
  {F : C1 ⟶ C2}
  (Fw : is_weak_equiv F)
  (P1 : Pullbacks C1)
  : Pullbacks C2.
Proof.
  intros z' x' y' fx' fy'.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x')).
  { apply isaprop_Pullback, C2_univ. }
  intros [x ix].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y')).
  { apply isaprop_Pullback, C2_univ. }
  intros [y iy].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw z')).
  { apply isaprop_Pullback, C2_univ. }
  intros [z iz].

  set (px := isotoid _ C2_univ ix).
  set (py := isotoid _ C2_univ iy).
  set (pz := isotoid _ C2_univ iz).
  induction px, py, pz.

  set (fx := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ fx').
  set (fy := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ fy').

  assert (p₁ : #F fx = fx'). {
    unfold fx ; now rewrite functor_on_fully_faithful_inv_hom.
  }
  assert (p₂ : #F fy = fy'). {
    unfold fy ; now rewrite functor_on_fully_faithful_inv_hom.
  }

  set (P := P1 _ _ _ fx fy).
  set (s' := weak_equiv_preserves_pullbacks Fw _ _ _ _ _ _ _ _ _
               (Pullbacks.p_func (pr12 P)) (pr22 P)).
  set (s := make_Pullback _ s').
  exact (pr1weq (transport_Pullback p₁ p₂) s).
Qed.

Lemma weak_equiv_into_univ_creates_haspullbacks
  {C1 C2 : category}
  (C2_univ : is_univalent C2)
  {F : C1 ⟶ C2}
  (Fw : is_weak_equiv F)
  (P1 : hasPullbacks C1)
  : hasPullbacks C2.
Proof.
  intros z' x' y' fx' fy'.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x')).
  { apply propproperty. }
  intros [x ix].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y')).
  { apply propproperty. }
  intros [y iy].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw z')).
  { apply propproperty. }
  intros [z iz].

  set (px := isotoid _ C2_univ ix).
  set (py := isotoid _ C2_univ iy).
  set (pz := isotoid _ C2_univ iz).
  induction px, py, pz.

  set (fx := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ fx').
  set (fy := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ fy').

  assert (p₁ : #F fx = fx'). {
    unfold fx ; now rewrite functor_on_fully_faithful_inv_hom.
  }
  assert (p₂ : #F fy = fy'). {
    unfold fy ; now rewrite functor_on_fully_faithful_inv_hom.
  }

  use (factor_through_squash _ _ (P1 _ _ _ fx fy)).
  { apply propproperty. }
  intro p.

  set (s' := weak_equiv_preserves_pullbacks Fw _ _ _ _ _ _ _ _ _
               (Pullbacks.p_func (pr12 p)) (pr22 p)).
  set (s := make_Pullback _ s').
  apply hinhpr.
  exact (pr1weq (transport_Pullback p₁ p₂) s).
Qed.
