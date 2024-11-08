(**
   In this file, we show that weak equivalences reflect pullbacks.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencesReflectsPullbacks₀.

  Context
    {C D : category}
      {F : C ⟶ D}
      (Fw : is_weak_equiv F)
      {x y z p : C}
      {fₓ : C ⟦x, z⟧}
      {fy : C ⟦y, z⟧}
      {pₓ : C ⟦p, x⟧}
      {py : C ⟦p, y⟧}
      (r : pₓ · fₓ = py · fy).

  Local Definition p_func : # F pₓ · # F fₓ = # F py · # F fy.
  Proof.
    refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
    apply maponpaths.
    exact r.
  Defined.

  Context (iFP : isPullback p_func).
  Let FP := make_Pullback _ iFP.

  Lemma weak_equiv_reflects_pullbacks_uvp_uniqueness
    {a : ob C}
    {q₁ : C⟦a, x⟧}
    {q₂ : C⟦a, y⟧}
    : isaprop (∑ hk : C⟦a, p⟧, hk · pₓ = q₁ × hk · py = q₂).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro; apply isapropdirprod; apply homset_property. }

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _).

    apply maponpaths.
    apply (MorphismsIntoPullbackEqual (pr22 FP)) ; simpl.
    - rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr12 φ₁ @ ! pr12 φ₂).
    - rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr22 φ₁ @ ! pr22 φ₂).
  Qed.

  Section WeakEquivalenceReflectsPullbackUniqueness.

    Context {a : C}
      {q₁ : C⟦a, x⟧}
      {q₂ : C⟦a, y⟧}
      (r' : q₁ · fₓ = q₂ · fy).

    Definition weak_equiv_reflects_pullbacks_uvp_existence₀
      : C ⟦ a, p ⟧.
    Proof.
      use (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ _).
      use (pr11 (iFP (F _) (#F q₁) (#F q₂) _)).
      abstract (rewrite <- ! functor_comp ;
                apply maponpaths ;
                exact r').
    Defined.

    Lemma weak_equiv_reflects_pullback_uvp_existence_first_projection
      : weak_equiv_reflects_pullbacks_uvp_existence₀ · pₓ = q₁.
    Proof.
      simpl.
      refine (! homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite functor_comp.
      etrans. {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (pr2 Fw) _ _)).
      }
      apply (pr21 (iFP _ _ _ _)).
    Qed.

    Lemma weak_equiv_reflects_pullback_uvp_existence_second_projection
      : weak_equiv_reflects_pullbacks_uvp_existence₀ · py = q₂.
    Proof.
      simpl.
      refine (! homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite functor_comp.
      etrans. {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (pr2 Fw) _ _)).
      }
      apply (pr21 (iFP _ _ _ _)).
    Qed.

    Definition weak_equiv_reflects_pullbacks_uvp_existence
      : ∑ hk : C ⟦ a, p ⟧, hk · pₓ = q₁ × hk · py = q₂.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact weak_equiv_reflects_pullbacks_uvp_existence₀.
      - exact weak_equiv_reflects_pullback_uvp_existence_first_projection.
      - exact weak_equiv_reflects_pullback_uvp_existence_second_projection.
    Defined.

  End WeakEquivalenceReflectsPullbackUniqueness.

  Lemma weak_equiv_reflects_pullbacks
    : isPullback r.
  Proof.
    intros a q₁ q₂ r'.
    use iscontraprop1.
    - apply weak_equiv_reflects_pullbacks_uvp_uniqueness.
    - exact (weak_equiv_reflects_pullbacks_uvp_existence r').
  Defined.

End WeakEquivalencesReflectsPullbacks₀.
