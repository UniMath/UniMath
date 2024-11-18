(**
The universal property of the Rezk completion states, 1-dimensionally, that every functor F into a univalent category factors (uniquely) through the Rezk completion.
The unique functor out of the Rezk completion is referred to as ``the lift of F''.
The contents in this file conclude that if F preserves pullbacks, then so does its lift.

In [weak_equiv_lifts_preserves_pullbacks], we show the following:
Assume F preserves all pullbacks in its domain.
Then, all equalizers in the codomain (the Rezk completion) are preserved by the lift.

In [weak_equiv_lifts_preserves_chosen_pullbacks_eq], we show the following:
Assume the involved categories have chosen pullbacks.
If F preserves the chosen pullbacks up to (propositional) equality, then so does it lift.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.

Local Open Scope cat.

Section LiftAlongWeakEquivalencePreservesPullbacks.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Fpb : preserves_pullback F).

  (* In this section, we show: preserves_pullback H *)

  Section LiftAlongWeakEquivalencePreservesEqualizers_subproofs.

    Context {y1 y2 py' py : C2}
      {fy : C2⟦y1, py'⟧}
      {gy : C2 ⟦y2, py'⟧}
      {π₁y : C2 ⟦py, y1⟧}
      {π₂y : C2⟦py, y2⟧}
      {q : π₁y · fy = π₂y · gy}
      {Fq : # H π₁y · # H fy = # H π₂y · # H gy}
      (ispby : isPullback q)
      {x1 x2 px px' : C1}
      (i1 : z_iso (G x1) y1)
      (i2 : z_iso (G x2) y2)
      (i : z_iso (G px) py)
      (i' : z_iso (G px') py').

    Let PB := (make_Pullback q ispby : Pullback fy gy).
    Let π₁x := ((fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₁y · z_iso_inv i1)).
    Let π₂x := ((fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₂y · z_iso_inv i2)).
    Let fx := ((fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i1 · fy · z_iso_inv i')).
    Let gx := ((fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i2 · gy · z_iso_inv i')).

    Lemma fully_faithful_inv_hom_of_pullback_diagram_commutes
      : π₁x · fx = π₂x · gx.
    Proof.
      unfold π₁x, fx, π₂x, gx.
      do 2 rewrite <- fully_faithful_inv_comp.
      apply maponpaths.
      rewrite ! assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply maponpaths_2.
      refine (_ @ q @ _).
      - apply maponpaths_2.
        refine (_ @ id_right _).
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply z_iso_after_z_iso_inv.
      - apply maponpaths_2.
        rewrite assoc'.
        refine (! id_right _ @ _).
        apply maponpaths.
        apply pathsinv0, z_iso_after_z_iso_inv.
    Qed.

    Lemma inv_of_pullback_leg_fy_commutes_with_image_modulo_isos
      : i1 · fy = # G fx · i'.
    Proof.
      unfold fx.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc'.
      apply maponpaths.
      refine (! id_right _ @ _).
      apply maponpaths, pathsinv0.
      apply (pr2 i').
    Qed.

    Lemma inv_of_pullback_leg_gy_commutes_with_image_modulo_isos
      : i2 · gy = # G gx · i'.
    Proof.
      unfold gx.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc'.
      apply maponpaths.
      refine (! id_right _ @ _).
      apply maponpaths, pathsinv0.
      apply (pr2 i').
    Qed.

    Lemma inv_of_pullback_first_projection_commutes_with_image_modulo_isos
      : i · π₁y = # G π₁x · i1.
    Proof.
      unfold π₁x.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc'.
      apply maponpaths.
      refine (! id_right _ @ _).
      apply maponpaths, pathsinv0.
      apply (pr2 i1).
    Qed.

    Lemma inv_of_pullback_second_projection_commutes_with_image_modulo_isos
      : # G π₂x · i2 = i · π₂y.
    Proof.
      unfold π₂x.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc'.
      apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (pr2 i2).
    Qed.

    Lemma fully_faithful_inv_hom_of_pullback_is_pullback
      : isPullback fully_faithful_inv_hom_of_pullback_diagram_commutes.
    Proof.
      use (weak_equiv_reflects_pullbacks Gw).
      use (Pullback_iso_squares q ispby).
      - exact i1.
      - exact i2.
      - exact i'.
      - exact i.
      - exact inv_of_pullback_leg_fy_commutes_with_image_modulo_isos.
      - exact inv_of_pullback_leg_gy_commutes_with_image_modulo_isos.
      - exact inv_of_pullback_first_projection_commutes_with_image_modulo_isos.
      - exact inv_of_pullback_second_projection_commutes_with_image_modulo_isos.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_leg_commute₀
      : # H (inv_from_z_iso i1) · pr1 α x1 · # F fx = # H fy · (# H (inv_from_z_iso i') · pr1 α px').
    Proof.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pr21 α _ _ _).
      }
      simpl.
      rewrite ! assoc.
      rewrite <- ! functor_comp.
      apply maponpaths_2, maponpaths.
      use z_iso_inv_on_left.
      rewrite assoc'.
      apply pathsinv0.
      use z_iso_inv_on_right.
      unfold fx.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. { do 2 apply maponpaths, (z_iso_after_z_iso_inv i'). }
      apply id_right.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_leg_commute₁
      : # H (inv_from_z_iso i2) · pr1 α x2 · # F gx = # H gy · (# H (inv_from_z_iso i') · pr1 α px').
    Proof.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pr21 α _ _ _).
      }
      simpl.
      rewrite ! assoc.
      rewrite <- ! functor_comp.
      apply maponpaths_2, maponpaths.
      use z_iso_inv_on_left.
      rewrite assoc'.
      apply pathsinv0.
      use z_iso_inv_on_right.
      unfold gx.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. { do 2 apply maponpaths, (z_iso_after_z_iso_inv i'). }
      apply id_right.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_first_projection_commute
      : # H (inv_from_z_iso i) · pr1 α px · # F π₁x = # H π₁y · (# H (inv_from_z_iso i1) · pr1 α x1).
    Proof.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pr21 α _ _ _).
      }
      simpl.
      rewrite ! assoc.
      rewrite <- ! functor_comp.
      apply maponpaths_2, maponpaths.
      use z_iso_inv_on_left.
      rewrite assoc'.
      apply pathsinv0.
      use z_iso_inv_on_right.
      unfold π₁x.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. { do 2 apply maponpaths, (z_iso_after_z_iso_inv i1). }
      apply id_right.
    Qed.

    Lemma images_of_fully_faithful_inv_hom_of_second_projection_commute
      : # H π₂y · (# H (inv_from_z_iso i2) · pr1 α x2) = # H (inv_from_z_iso i) · pr1 α px · # F π₂x.
    Proof.
      unfold z_iso_comp, functor_on_z_iso.
      simpl.
      rewrite assoc'.
      etrans. 2: {
        apply maponpaths.
        apply (pr21 α _ _ _).
      }
      simpl.
      rewrite ! assoc.
      rewrite <- ! functor_comp.
      apply maponpaths_2, maponpaths.
      apply pathsinv0.
      use z_iso_inv_on_left.
      rewrite assoc'.
      apply pathsinv0.
      use z_iso_inv_on_right.
      unfold π₂x.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      etrans. { do 2 apply maponpaths, (z_iso_after_z_iso_inv i2). }
      apply id_right.
    Qed.

    Lemma pullback_is_preserved_after_lift
      : isPullback Fq.
    Proof.
      use (Pullback_iso_squares _
             (Fpb _ _ _ _ _ _ _ _
                fully_faithful_inv_hom_of_pullback_diagram_commutes
                (Pullbacks.p_func fully_faithful_inv_hom_of_pullback_diagram_commutes)
                fully_faithful_inv_hom_of_pullback_is_pullback
          )).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i1)) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i2)) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i')) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i)) (_ ,, pr2 α _)).
      - exact images_of_fully_faithful_inv_hom_of_leg_commute₀.
      - exact images_of_fully_faithful_inv_hom_of_leg_commute₁.
      - exact images_of_fully_faithful_inv_hom_of_first_projection_commute.
      - exact images_of_fully_faithful_inv_hom_of_second_projection_commute.
    Defined.

  End LiftAlongWeakEquivalencePreservesEqualizers_subproofs.

  Lemma weak_equiv_lifts_preserves_pullbacks
    : preserves_pullback H.
  Proof.
    intros y1 y2 py' py fy gy π₁y π₂y q Fq ispby.
    set (PB := make_Pullback _ ispby).

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
    { apply isaprop_isPullback. }
    intros [x1 i1].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
    { apply isaprop_isPullback. }
    intros [x2 i2].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw py)).
    { apply isaprop_isPullback. }
    intros [px i].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw py')).
    { apply isaprop_isPullback. }
    intros [px' i'].

    exact (pullback_is_preserved_after_lift ispby i1 i2 i i').
  Qed.

End LiftAlongWeakEquivalencePreservesPullbacks.

Section LiftAlongWeakEquivalencePreservesChosenPullbacksUptoEquality.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (P₁ : Pullbacks C1)
    (P₂ : Pullbacks (pr1 C2))
    (P₃ : Pullbacks (pr1 C3))
    (Gw : is_weak_equiv G)
    (Fpb : preserves_chosen_pullbacks_eq F P₁ P₃).

  Section LiftAlongWeakEquivalencePreservesChosenPullbacksUptoEqualityAfterInduction.

    Context {x y z : C1}
      (f' : C2⟦G x, G z⟧)
      (g' : C2⟦G y, G z⟧).

    Lemma lift_preserves_chosen_pullbacks_uptoeq_after_isotoid_induction
      : ∥ H (P₂ (G z) (G x) (G y) f' g') = P₃ (H (G z)) (H (G x)) (H (G y)) (# H f') (# H g') ∥.
    Proof.

      set (f := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw) _ _ f')).
      set (g := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw) _ _ g')).

      use (factor_through_squash _ _ (Fpb x y z f g)).
      { apply isapropishinh. }
      intro v.
      set (w := weak_equiv_preserves_pullbacks_eq Gw (pr2 C2) P₁ P₂ x y z f g).
      use (factor_through_squash _ _ w).
      { apply isapropishinh. }
      clear w ; intro w.

      apply hinhpr.

      assert (pf_f : #G f = f'). {
        unfold f ; now rewrite functor_on_fully_faithful_inv_hom.
      }
      assert (pf_g : #G g = g'). {
        unfold g ; now rewrite functor_on_fully_faithful_inv_hom.
      }

      rewrite pf_f in w.
      rewrite pf_g in w.
      etrans. {
        apply maponpaths.
        exact (! w).
      }
      clear w.

      set (ϕ₄ := nat_z_iso_pointwise_z_iso α (P₁ z x y f g)).
      set (ψ := isotoid _ (pr2 C3) ϕ₄).
      refine (ψ @ _).
      refine (v @ _).

      use (isotoid _ (pr2 C3)).

      pose (ϕ₁ := nat_z_iso_pointwise_z_iso α x).
      pose (ϕ₂ := nat_z_iso_pointwise_z_iso α y).
      pose (ϕ₃ := z_iso_inv (nat_z_iso_pointwise_z_iso α z)).
      pose (ψ₁ := isotoid _ (pr2 C3) ϕ₁).
      pose (ψ₂ := isotoid _ (pr2 C3) ϕ₂).
      pose (ψ₃ := isotoid _ (pr2 C3) ϕ₃).

      use (Pullback_eq P₃ ψ₁ ψ₂ ψ₃).
      - rewrite <- pf_f.
        unfold ψ₁, ψ₃.
        do 2 rewrite idtoiso_isotoid.
        etrans. {
          apply maponpaths_2.
          exact (! pr21 α _ _ _).
        }
        apply z_iso_inv_to_right.
        apply idpath.
      - rewrite <- pf_g.
        unfold ψ₂, ψ₃.
        do 2 rewrite idtoiso_isotoid.
        etrans. {
          apply maponpaths_2.
          exact (! pr21 α _ _ _).
        }
        apply z_iso_inv_to_right.
        apply idpath.
    Qed.

  End LiftAlongWeakEquivalencePreservesChosenPullbacksUptoEqualityAfterInduction.

  Lemma weak_equiv_lifts_preserves_chosen_pullbacks_eq
    : preserves_chosen_pullbacks_eq H P₂ P₃.
  Proof.
    intros x' y' z' f' g'.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x')).
    { apply isapropishinh. }
    intros [x ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y')).
    { apply isapropishinh. }
    intros [y iy].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw z')).
    { apply isapropishinh. }
    intros [z iz].

    induction (isotoid _ (pr2 C2) ix).
    induction (isotoid _ (pr2 C2) iy).
    induction (isotoid _ (pr2 C2) iz).

    exact (lift_preserves_chosen_pullbacks_uptoeq_after_isotoid_induction f' g').
  Qed.

End LiftAlongWeakEquivalencePreservesChosenPullbacksUptoEquality.
