Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencePreservationsEqualizers₀.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : is_weak_equiv F)
    {x y e : C}
    {f₁ f₂ : C ⟦ x, y ⟧}
    {h : C ⟦ e, x ⟧}
    {p : h · f₁ = h · f₂}
    (* {Fp : # F h · # F f₁ = # F h · # F f₂} *)
    (iE : isEqualizer f₁ f₂ h p)
    {e' : D}
    (h' : D ⟦e', F x⟧)
    (p' : h' · # F f₁ = h' · # F f₂)
    {e'' : C}
    (i : z_iso (F e'') e').

  Let E := make_Equalizer _ _ _ _ iE.
  (* Let ϕ : C⟦e'', x⟧ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (i · h'). *)

  Lemma weak_equiv_preserves_equalizers_unique
    : isaprop (∑ φ : D⟦e', F e⟧, φ · # F h = h').
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply homset_property. }
    use (cancel_z_iso' i).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).

    apply maponpaths.
    use (isEqualizerInsEq iE).
    refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
    apply maponpaths.
    simpl.
    rewrite ! functor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
    }
    refine (! _).

    etrans. {
      apply maponpaths_2.
      apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
    }
    rewrite ! assoc'.
    apply maponpaths.
    exact (pr2 φ₂ @ ! pr2 φ₁).
  Qed.

End WeakEquivalencePreservationsEqualizers₀.

Definition weak_equiv_preserves_equalizers
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_equalizer F.
Proof.
  intros x y e f₁ f₂ h p Fp iE.
  pose (E := make_Equalizer _ _ _ _ iE).
  intros e' h' p'.
  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw e')).
  intros [e'' i].

  apply (iscontraprop1 (weak_equiv_preserves_equalizers_unique Fw iE h' i)).
  set (ϕ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (i · h')).
  assert (q : ϕ · f₁ = ϕ · f₂).
  {
    use (faithful_reflects_morphism_equality F (pr2 Fw)).
    do 2 rewrite functor_comp.
    unfold ϕ.
    rewrite functor_on_fully_faithful_inv_hom.
    do 2 rewrite assoc'.
    apply maponpaths.
    exact p'.
  }
  exists (z_iso_inv i · #F (pr11 (iE _ _ q))).

  rewrite assoc'.
  rewrite <- (functor_comp F).
  etrans. {
    do 2 apply maponpaths.
    exact (pr21 (iE _ _ q)).
  }
  etrans. {
    apply maponpaths.
    apply functor_on_fully_faithful_inv_hom.
  }
  rewrite assoc.
  etrans. {
    apply maponpaths_2.
    apply z_iso_after_z_iso_inv.
  }
  apply id_left.
Qed.

Definition weak_equiv_preserves_chosen_equalizers
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (BP : Equalizers C)
  : preserves_chosen_equalizer BP F.
Proof.
  intros x y f g p.
  use (weak_equiv_preserves_equalizers Fw).
  - apply EqualizerEqAr.
  - apply isEqualizer_Equalizer.
Qed.

Definition weak_equiv_preserves_equalizers_eq
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (Duniv : is_univalent D)
  (E₁ : Equalizers C) (E₂ : Equalizers D)
  : preserves_chosen_equalizers_eq F E₁ E₂.
Proof.
  intros x y f g.
  apply hinhpr.
  apply Duniv.
  set (Fe := weak_equiv_preserves_equalizers Fw).

  set (e₂ := (E₂ _ _ (#F f) (#F g))).
  use (z_iso_from_Equalizer_to_Equalizer
         (make_Equalizer _ _ _ _ (Fe _ _ _ _ _ _ _ _ (pr22 (E₁ _ _ f g))))
         (E₂ _ _ (#F f) (#F g))
        ).
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  apply E₁.
Qed.
