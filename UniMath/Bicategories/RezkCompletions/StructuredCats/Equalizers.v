(*
In this file, we show how the Rezk completion of a category has equalizers if the original category has equalizers.
Hence, categories with equalizers admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithEqualizersHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with equalizers (up to propositional truncation).
2. BicatOfCategoriesWithChosenEqualizersHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with chosen equalizers.
*)

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

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Local Open Scope cat.

Section BicatOfCategoriesWithEqualizersHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).

  Lemma weak_equiv_lifts_preserves_equalizers
    {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    : preserves_equalizer F → preserves_equalizer H.
  Proof.
    intros Feq x' y' a' f₁' f₂' e' r Fr iEe.

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

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x')).
    { apply isaprop_isEqualizer. }
    intros [x ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y')).
    { apply isaprop_isEqualizer. }
    intros [y iy].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw a')).
    { apply isaprop_isEqualizer. }
    intros [a ia].

    set (f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (pr1 ix · f₁' · z_iso_inv iy)).
    set (f₂ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (pr1 ix · f₂' · pr12 iy)).
    set (e := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (ia · e' · pr12 ix)).

    assert (p : e · f₁ = e · f₂).
    {
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
    }

    assert (pf : is_z_isomorphism_mor (pr2 α a) · # H ia · # H e' · (# H (inv_from_z_iso ix) · α x) = # F e).
    {
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
    }

    assert (pf' :  # H f₁' · (# H (inv_from_z_iso iy) · α y) = # H (inv_from_z_iso ix) · α x · # F f₁).
    {
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
    }

    assert (pf'' :  # H f₂' · (# H (inv_from_z_iso iy) · α y) = # H (inv_from_z_iso ix) · α x · # F f₂).
    {
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
    }

    assert (pf₀ : isEqualizer f₁ f₂ e p). {
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
    }

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

  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).
  Let RR := (disp_psfunctor_on_cat_to_univ_cat disp_bicat_have_equalizers
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_equalizers)).
  Definition cat_with_equalizers_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw [E₁ _].
      refine (_ ,, tt).
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
      use (EqualizerOfIso f' g' iₓ (z_iso_inv iy)).
      unfold f₁, g₁ in tE.
      do 2 rewrite functor_on_fully_faithful_inv_hom in tE.
      exact tE.
    - cbn ; intros C [E _].
      refine (tt ,, _).
      apply weak_equiv_preserves_equalizers.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α E₁ E₂ E₃ Gw.
      intros [t Feq].
      exact (tt ,, weak_equiv_lifts_preserves_equalizers C2 C3 α Gw Feq).
  Defined.

End BicatOfCategoriesWithEqualizersHasRezkCompletion.

Section BicatOfCategoriesWithChosenEqualizersHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_chosen_equalizers.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_equalizers)).

  Definition weak_equiv_preserves_equalizer_univ
    {C1 C2 : category}
    (C2_univ : is_univalent C2)
    {F : C1 ⟶ C2}
    (Fw : is_weak_equiv F)
    (C1_E : Equalizers C1)
    : Equalizers C2.
  Proof.
    intros x' y' f g.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x')).
    { apply isaprop_Equalizer, C2_univ. }
    intros [x ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y')).
    { apply isaprop_Equalizer, C2_univ. }
    intros [y iy].
    apply (EqualizerOfIso f g ix (z_iso_inv iy)).
    set (f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (ix · f · z_iso_inv iy)).
    set (g₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)) _ _ (ix · g · z_iso_inv iy)).
    set (t := weak_equiv_preserves_chosen_equalizers Fw C1_E _ _ f₁ g₁).
    unfold f₁, g₁ in t.
    do 2 rewrite functor_on_fully_faithful_inv_hom in t.
    use (make_Equalizer _ _ _ _ (t _)).
    clear t.

    assert (p₁ :  (ix · f · z_iso_inv iy = #F f₁)). {
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    }
    assert (p₂ :  (ix · g · z_iso_inv iy = #F g₁)). {
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    }
    rewrite p₁, p₂.
    do 2 rewrite <- functor_comp.
    apply maponpaths.

    assert (pf₀ : fully_faithful_inv_hom (ff_from_weak_equiv F Fw) x y (# F g₁) = g₁).
    { apply fully_faithful_inv_hom_is_inv. }
    assert (pf₁ : fully_faithful_inv_hom (ff_from_weak_equiv F Fw) x y (# F f₁) = f₁).
    { apply fully_faithful_inv_hom_is_inv. }
    rewrite pf₀, pf₁.

    apply EqualizerEqAr.
  Defined.

  Lemma weak_equiv_lifts_preserves_chosen_equalizers_eq {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (E₁ : Equalizers C1)
    (E₂ : Equalizers (pr1 C2))
    (E₃ : Equalizers (pr1 C3))
    (Gw : is_weak_equiv G)
    : preserves_chosen_equalizers_eq F E₁ E₃
      → preserves_chosen_equalizers_eq H E₂ E₃.
  Proof.
    intros Feq x' y' f' g'.

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

    set (f₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ f').
    set (g₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ g').

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

  Definition cat_with_chosen_equalizers_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw C1_prod.
      exact (weak_equiv_preserves_equalizer_univ C2_univ Fw (pr1 C1_prod) ,, tt).
    - intros C C1_prod.
      refine (tt ,, _).
      use weak_equiv_preserves_equalizers_eq.
      + apply η_weak_equiv.
      + exact (pr2 (pr1 LUR C)).
    - intros C1 C2 C3 F G H α E₁ E₂ E₃ Gw.
      intros [t Feq].
      exists tt.
      exact (weak_equiv_lifts_preserves_chosen_equalizers_eq C2 C3 α (pr1 E₁) (pr1 E₂) (pr1 E₃) Gw Feq).
  Defined.

End BicatOfCategoriesWithChosenEqualizersHasRezkCompletion.
