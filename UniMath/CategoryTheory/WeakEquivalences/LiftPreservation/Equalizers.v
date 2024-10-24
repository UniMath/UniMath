Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Limits.Equalizers.

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

  Section A.

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

    Let p : (e · f₁ = e · f₂).
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

    Let pf : (is_z_isomorphism_mor (pr2 α a) · # H ia · # H e' · (# H (inv_from_z_iso ix) · α x) = # F e).
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

    Let pf' : # H f₁' · (# H (inv_from_z_iso iy) · α y) = # H (inv_from_z_iso ix) · α x · # F f₁.
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

    Let pf'' : # H f₂' · (# H (inv_from_z_iso iy) · α y) = # H (inv_from_z_iso ix) · α x · # F f₂.
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

    Lemma pf₀ : isEqualizer f₁ f₂ e p.
    Proof.
      use (@weak_equiv_reflects_equalizers _ _ _ Gw x y a f₁ f₂ e p).
      use (isEqualizerUnderIso _ _ _ _ _ _ _ iEe).
      - exact (z_iso_inv ia).
      - exact (z_iso_inv ix).
      - exact (z_iso_inv iy).
      - unfold e.
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
      - unfold f₁.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite assoc'.
        etrans. {
          apply maponpaths.
          apply (z_iso_inv_after_z_iso (z_iso_inv iy)).
        }
        now rewrite id_right.
      - unfold f₂.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite assoc'.
        etrans. {
          apply maponpaths.
          apply (z_iso_inv_after_z_iso (z_iso_inv iy)).
        }
        now rewrite id_right.
    Qed.

    Lemma equalizer_is_preserved_after_lift
      (Fr : # H e' · # H f₁' = # H e' · # H f₂')
      : isEqualizer (# H f₁') (# H f₂') (# H e') Fr.
    Proof.
      set (αi := nat_z_iso_inv α).
      use (isEqualizerUnderIso _ _ _ _ _ _ _ (Feq x y a f₁ f₂ e p (Equalizers.p_func (p := p)) _)).
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact ia.
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact ix.
      - use (z_iso_comp (_ ,, pr2 αi _)) ; simpl ; apply functor_on_z_iso.
        exact iy.
      - exact (! pf).
      - exact pf'.
      - apply pf''.
      - apply pf₀.
    Qed.

  End A.

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
