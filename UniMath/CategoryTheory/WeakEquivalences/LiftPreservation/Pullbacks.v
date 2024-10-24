Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Limits.Pullbacks.

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

  Section A.

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

    Lemma pf₀ : π₁x · fx = π₂x · gx.
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

    Lemma pf : isPullback pf₀.
    Proof.
      use (@weak_equiv_reflects_pullbacks _ _ _ Gw x1 x2 px' px fx gx π₁x π₂x pf₀).
      use (Pullback_iso_squares q ispby).
      - exact i1.
      - exact i2.
      - exact i'.
      - exact i.
      - unfold fx.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite ! assoc'.
        apply maponpaths.
        refine (! id_right _ @ _).
        apply maponpaths, pathsinv0.
        apply (pr2 i').
      - unfold gx.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite ! assoc'.
        apply maponpaths.
        refine (! id_right _ @ _).
        apply maponpaths, pathsinv0.
        apply (pr2 i').
      - unfold π₁x.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite ! assoc'.
        apply maponpaths.
        refine (! id_right _ @ _).
        apply maponpaths, pathsinv0.
        apply (pr2 i1).
      - unfold π₂x.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite ! assoc'.
        apply maponpaths.
        refine (_ @ id_right _).
        apply maponpaths.
        apply (pr2 i2).
    Qed.

    Lemma pf_0
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

    Lemma pf_1
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

    Lemma pf_2
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

    Lemma pf_3
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
      use (Pullback_iso_squares _ (Fpb _ _ _ _ _ _ _ _ pf₀ (Pullbacks.p_func pf₀) pf)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i1)) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i2)) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i')) (_ ,, pr2 α _)).
      - exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i)) (_ ,, pr2 α _)).
      - exact pf_0.
      - exact pf_1.
      - exact pf_2.
      - exact pf_3.
    Qed.

  End A.

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
