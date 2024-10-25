(**
The universal property of the Rezk completion states, 1-dimensionally, that every functor F into a univalent category factors (uniquely) through the Rezk completion.
The unique functor out of the Rezk completion is referred to as ``the lift of F''.
The contents in this file conclude that if F preserves equalizers, then so does its lift.

In [weak_equiv_lifts_preserves_equalizers], we show the following:
Assume F preserves all equalizers in its domain.
Then all equalizers in the Rezk completion (of the domain) are also preserved.

In [weak_equiv_lifts_preserves_chosen_equalizers_eq], we show the following:
Assume all the involved categories have chosen equalizers.
If F preserves the chosen equalizers up to (propositional) equality, then so does it lift.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Equalizers.

Local Open Scope cat.

Section LiftAlongWeakEquivalencePreservesEqualizers.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Feq : preserves_equalizer F).

  (* In this section, we show: preserves_equalizer H *)

  Section LiftAlongWeakEquivalencePreservesEqualizers_subproofs.

    (*
      An equalizer diagram (in C₂) is given: [a' -e'-> x' -={f₁', f₂'}=-> y'].
      We show that [H a' -{H e'}-> H x' -={H f₁', H f₂'}=-> H y'], is an equalizer diagram (in C₃).
      Since we prove a proposition, eso'ness of G implies that the diagram (e',f₁',g₁') is in the image of G (in combination with fully faithfulness).
      This, we call a -e-> x -={f₁, f₂}=-> y.
      Furthermore, we know that weak equivalences reflect finite limits.
      Hence, (e, f₁, f₂) is an equalizer diagram.
      By assumption on F, we have that [F a -{F e}-> F x -={F f₁, F f₂}=-> F y] is an equalizer diagram in C₃.
      The result now follows since F ≅ G · H
     *)

    Context {x' y' a' : C2}
      {f₁' f₂' : C2 ⟦ x', y' ⟧}
      {e' : C2 ⟦ a', x' ⟧}
      {r : e' · f₁' = e' · f₂'}
      (iEe : isEqualizer f₁' f₂' e' r)
      {x y a : C1}
      (ix : z_iso (G x) x')
      (iy : z_iso (G y) y')
      (ia : z_iso (G a) a').

    Let f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (pr1 ix · f₁' · z_iso_inv iy).
    Let f₂ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (pr1 ix · f₂' · pr12 iy).
    Let e := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (ia · e' · pr12 ix).

    Lemma fully_faithful_inv_hom_of_equalizer_diagram_commutes
      : e · f₁ = e · f₂.
    Proof.
      unfold f₁, f₂, e.
      repeat (rewrite <- fully_faithful_inv_comp).
      apply maponpaths.
      repeat rewrite assoc'.
      apply maponpaths.
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        apply (pr2 ix).
      }
      etrans. {
        rewrite id_left.
        rewrite assoc.
        apply maponpaths_2.
        exact r.
      }
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0.
      refine (assoc _ _ _ @ _).
      etrans. {
        apply maponpaths_2.
        apply (pr2 ix).
      }
      apply id_left.
    Qed.

    Lemma inv_of_equalizer_map_commutes_with_image_modulo_isos
      : e' = z_iso_inv ia · # G e · pr12 (z_iso_inv ix).
    Proof.
      unfold e.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left.
      rewrite assoc'.
      apply pathsinv0.
      etrans. {
        apply maponpaths.
        apply (z_iso_inv_after_z_iso (z_iso_inv ix)).
      }
      apply id_right.
    Qed.

    Lemma inv_of_f₁'_commutes_with_image_modulo_isos
      : # G f₁ · pr12 (z_iso_inv iy) = pr12 (z_iso_inv ix) · f₁'.
    Proof.
      unfold f₁.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply (z_iso_inv_after_z_iso (z_iso_inv iy)).
      }
      now rewrite id_right.
    Qed.

    Lemma inv_of_f₂'_commutes_with_image_modulo_isos
      : # G f₂ · pr12 (z_iso_inv iy) = pr12 (z_iso_inv ix) · f₂'.
    Proof.
      unfold f₂.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply (z_iso_inv_after_z_iso (z_iso_inv iy)).
      }
      now rewrite id_right.
    Qed.

    Lemma fully_faithful_inv_hom_of_equalizer_is_equalizer
      : isEqualizer f₁ f₂ e fully_faithful_inv_hom_of_equalizer_diagram_commutes.
    Proof.
      use (weak_equiv_reflects_equalizers Gw).
      use (isEqualizerUnderIso _ _ _ _ _ _ _ iEe).
      - exact (z_iso_inv ia).
      - exact (z_iso_inv ix).
      - exact (z_iso_inv iy).
      - exact inv_of_equalizer_map_commutes_with_image_modulo_isos.
      - exact inv_of_f₁'_commutes_with_image_modulo_isos.
      - exact inv_of_f₂'_commutes_with_image_modulo_isos.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_equalizer_map_commute
      : is_z_isomorphism_mor (pr2 α a) · # H ia · # H e' · (# H (inv_from_z_iso ix) · α x)
        = # F e.
    Proof.
      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp H).
      }
      etrans. {
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp H).
      }
      refine (assoc' _ _ _ @ _).
      use (z_iso_inv_on_right _ _ _ (_ ,, pr2 α a)).
      simpl.
      refine (_ @ pr21 α _ _ _).
      apply maponpaths_2.
      simpl; apply maponpaths.
      unfold e.
      apply pathsinv0.
      apply functor_on_fully_faithful_inv_hom.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_f₁'_commute
      : # H f₁' · (# H (inv_from_z_iso iy) · α y)
        = # H (inv_from_z_iso ix) · α x · # F f₁.
    Proof.
      refine (assoc _ _ _ @ _).
      rewrite <- functor_comp.
      refine (_ @ assoc _ _ _).
      etrans.
      2: apply maponpaths, (pr21 α _ _ f₁).
      simpl.
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      unfold f₁.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      apply maponpaths_2.
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply pathsinv0, z_iso_after_z_iso_inv.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_f₂'_commute
      : # H f₂' · (# H (inv_from_z_iso iy) · α y)
        = # H (inv_from_z_iso ix) · α x · # F f₂.
    Proof.
      refine (assoc _ _ _ @ _).
      rewrite <- functor_comp.
      refine (_ @ assoc _ _ _).
      etrans.
      2: apply maponpaths, (pr21 α _ _ f₂).
      simpl.
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      unfold f₂.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      apply maponpaths_2.
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply pathsinv0, z_iso_after_z_iso_inv.
    Qed.

    Lemma equalizer_is_preserved_after_lift
      (Fr : # H e' · # H f₁' = # H e' · # H f₂')
      : isEqualizer (# H f₁') (# H f₂') (# H e') Fr.
    Proof.
      set (αi := nat_z_iso_inv α).
      use (isEqualizerUnderIso _ _ _ _ _ _ _
             (Feq x y a f₁ f₂ e
                fully_faithful_inv_hom_of_equalizer_diagram_commutes
                (Equalizers.p_func (p := fully_faithful_inv_hom_of_equalizer_diagram_commutes)) _)).
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact ia.
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact ix.
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact iy.
      - exact (! images_of_fully_faithful_inv_hom_of_equalizer_map_commute).
      - exact images_of_fully_faithful_inv_hom_of_f₁'_commute.
      - exact images_of_fully_faithful_inv_hom_of_f₂'_commute.
      - exact fully_faithful_inv_hom_of_equalizer_is_equalizer.
    Defined.

  End LiftAlongWeakEquivalencePreservesEqualizers_subproofs.

  Lemma weak_equiv_lifts_preserves_equalizers
    : preserves_equalizer H.
  Proof.
    intros x' y' a' f₁' f₂' e' r Fr iEe.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x')).
    { apply isaprop_isEqualizer. }
    intros [x ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y')).
    { apply isaprop_isEqualizer. }
    intros [y iy].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw a')).
    { apply isaprop_isEqualizer. }
    intros [a ia].

    exact (equalizer_is_preserved_after_lift iEe ix iy ia Fr).
  Qed.

End LiftAlongWeakEquivalencePreservesEqualizers.

Section LiftAlongWeakEquivalencePreservesChosenEqualizersUptoEquality.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (E₁ : Equalizers C1)
    (E₂ : Equalizers (pr1 C2))
    (E₃ : Equalizers (pr1 C3))
    (Gw : is_weak_equiv G)
    (Feq : preserves_chosen_equalizers_eq F E₁ E₃).

  Section LiftAlongWeakEquivalencePreservesChosenEqualizersUptoEqualityAfterInduction.

    Context {x y : C1}
      (f' g' : C2⟦G x, G y⟧).

    Let f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ f'.
    Let g₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ g'.

    Lemma lift_preserves_chosen_equalizers_uptoeq_after_isotoid_induction
      : ∥ H (E₂ (G x) (G y) f' g') = E₃ (H (G x)) (H (G y)) (# H f') (# H g') ∥.
    Proof.

      use (factor_through_squash _ _ (Feq x y f₁ g₁)).
      { apply isapropishinh. }
      intro pf_F.

      set (Geq := weak_equiv_preserves_equalizers_eq Gw (pr2 C2) E₁ E₂).
      use (factor_through_squash _ _ (Geq x y f₁ g₁)).
      { apply isapropishinh. }
      intro pf_G.
      clear Geq.

      assert (p₀ : f' = #G f₁).
      { apply pathsinv0, functor_on_fully_faithful_inv_hom. }
      assert (p₁ : g' = #G g₁).
      { apply pathsinv0, functor_on_fully_faithful_inv_hom. }

      apply hinhpr.
      rewrite p₀, p₁.
      clear p₀ p₁.

      etrans. {
        apply maponpaths.
        exact (! pf_G).
      }
      clear pf_G.
      set (ϕ := isotoid _ (pr2 C3) (nat_z_iso_pointwise_z_iso α (E₁ _ _ f₁ g₁))).
      refine (ϕ @ _).
      refine (pf_F @ _) ; clear pf_F.
      use (isotoid _ (pr2 C3)).

      pose (ϕ₁ := nat_z_iso_pointwise_z_iso α x).
      pose (ϕ₂ := nat_z_iso_pointwise_z_iso α y).
      pose (ψ₁ := isotoid _ (pr2 C3) ϕ₁).
      pose (ψ₂ := isotoid _ (pr2 C3) (z_iso_inv ϕ₂)).

      use (Equalizer_eq E₃ (f := #F f₁) (g := #F g₁) ψ₁ ψ₂).
      - unfold ψ₁, ψ₂.
        do 2 rewrite idtoiso_isotoid.
        etrans. {
          apply maponpaths_2.
          exact (! pr21 α _ _ _).
        }
        apply z_iso_inv_to_right.
        apply idpath.
      - unfold ψ₁, ψ₂.
        do 2 rewrite idtoiso_isotoid.
        etrans. {
          apply maponpaths_2.
          exact (! pr21 α _ _ _).
        }
        apply z_iso_inv_to_right.
        apply idpath.
    Qed.

  End LiftAlongWeakEquivalencePreservesChosenEqualizersUptoEqualityAfterInduction.

  Lemma weak_equiv_lifts_preserves_chosen_equalizers_eq
    : preserves_chosen_equalizers_eq H E₂ E₃.
  Proof.
    intros x' y' f' g'.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x')).
    { apply isapropishinh. }
    intros [x ix].

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y')).
    { apply isapropishinh. }
    intros [y iy].

    pose (j1 := isotoid _ (pr2 C2) ix).
    pose (j2 := isotoid _ (pr2 C2) iy).

    induction j1.
    induction j2.

    exact (lift_preserves_chosen_equalizers_uptoeq_after_isotoid_induction f' g').
  Qed.

End LiftAlongWeakEquivalencePreservesChosenEqualizersUptoEquality.
