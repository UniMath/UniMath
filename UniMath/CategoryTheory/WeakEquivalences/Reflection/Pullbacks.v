Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

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
      (* (Fr : # F pₓ · # F fₓ = # F py · # F fy). *)

  Local Definition p_func : # F pₓ · # F fₓ = # F py · # F fy.
  Proof.
    refine (! functor_comp _ _ _ @ _ @ functor_comp _ _ _).
    apply maponpaths.
    exact r.
  Defined.

  Context (iFP : isPullback p_func).
  Let FP := make_Pullback _ iFP.

  Lemma uvp_isPullback_isaprop_from_image_weq
    {a : ob C}
    {q₁ : C⟦a, x⟧}
    {q₂ : C⟦a, y⟧}
    (* (r' : = ) *)
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

  Lemma weak_equiv_reflects_pullbacks
    : isPullback r.
  Proof.
    unfold isPullback.
    intros a q₁ q₂ r'.
    use iscontraprop1.
    - apply uvp_isPullback_isaprop_from_image_weq.
    - simple refine (_ ,, _ ,, _).
      + use (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ _).
        use (pr11 (iFP (F _) (#F q₁) (#F q₂) _)).
        abstract (rewrite <- ! functor_comp ;
                  apply maponpaths ;
                  exact r').
      + simpl.
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
      + simpl.
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

End WeakEquivalencesReflectsPullbacks₀.
