(**
   In this file, we show that weak equivalences reflect equalizers.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencesReflectsEqualizers₀.

  Context
    {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
      {x y e : C}
      {f₁ f₂ : C ⟦ x, y ⟧}
      {h : C ⟦ e, x ⟧}
      {p : h · f₁ = h · f₂}.

  Local Definition p_func : # F h · # F f₁ = # F h · # F f₂.
  Proof.
    do 2 rewrite <- functor_comp.
    apply maponpaths.
    exact p.
  Qed.

  Context (iEF : isEqualizer (#F f₁) (#F f₂) (#F h) p_func).

  Lemma uvp_isEqualizer_isaprop_from_image_weq
    {e' : C}
    {h' : C ⟦ e', x ⟧}
    (p' : h' · f₁ = h' · f₂)
    : isaprop (∑ φ : C ⟦ e', e ⟧, φ · h = h').
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro; apply homset_property. }

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _).

    apply maponpaths.
    cbn.
    apply (EqualizerInsEq (make_Equalizer _ _ _ _ iEF)).
    cbn.
    rewrite <- ! functor_comp.
    apply maponpaths.
    exact (pr2 φ₁ @ ! pr2 φ₂).
  Qed.

  Lemma weak_equiv_reflects_equalizers
    : isEqualizer f₁ f₂ h p.
  Proof.
    intros e' h' p'.
    use iscontraprop1.
    - apply uvp_isEqualizer_isaprop_from_image_weq.
      exact p'.
    - use tpair.
      + use (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ _).
        use (pr11 (iEF (F e') (#F h') _)).
        abstract (rewrite <- ! functor_comp ;
                  apply maponpaths ;
                  exact p').
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
        apply (pr21 (iEF _ _ _)).
  Qed.

End WeakEquivalencesReflectsEqualizers₀.
