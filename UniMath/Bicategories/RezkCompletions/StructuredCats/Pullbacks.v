(*
In this file, we show how the Rezk completion of a categories has a suitable terminal object (in terms of preservation) if the original category has a terminal object.
Hence, categories with terminal objects admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a terminal object (up to propositional truncation).
2. BicatOfCategoriesWithChosenTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a chosen terminal object.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
(* Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful. *)

(* Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction. *)

Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Pullbacks.


Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

(* Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles. *)
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Local Open Scope cat.

Section BicatOfCategoriesWithPullbackHasRezkCompletion.

  Definition cat_with_pullback_has_RezkCompletion
    (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C))
    : disp_left_universal_arrow
        LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_have_pullbacks
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_pullbacks)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw [P1 t].
      clear t.
      refine (_ ,, tt).
      simpl in *.
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

      set (P := P1 _ _ _ fx fy).
      set (s' := weak_equiv_preserves_pullbacks Fw _ _ _ _ _ _ _ _ _
                  (Pullbacks.p_func (pr12 P)) (pr22 P)).
      set (s := make_Pullback _ s').

      assert (p₁ : #F fx = fx'). {
        unfold fx.
        now rewrite functor_on_fully_faithful_inv_hom.
      }
      assert (p₂ : #F fy = fy'). {
        unfold fy.
        now rewrite functor_on_fully_faithful_inv_hom.
      }

      exact (pr1weq (transport_Pullback p₁ p₂) s).
    - intros C pb.
      refine (tt ,, _).
      apply weak_equiv_preserves_pullbacks.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α P1 P2 P3 Gw.
      intros [t Fpb].
      exists tt.
      use (weak_equiv_lifts_preserves_pullbacks C2 C3 α _ _ _ Gw Fpb)
      ; intro ; intros ; apply hinhpr.
      + simpl in P1 ; apply P1.
      + simpl in P2 ; apply P2.
      + simpl in P3 ; apply P3.
  Qed.

End BicatOfCategoriesWithPullbackHasRezkCompletion.

Section BicatOfCategoriesWithChosenPullbackHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_chosen_pullbacks.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_pullbacks)).

  Definition weak_equiv_preserves_pullbacks_univ
    {C1 C2 : category}
    (C2_univ : is_univalent C2)
    {F : C1 ⟶ C2}
    (Fw : is_weak_equiv F)
    (P1 : Pullbacks C1)
    : Pullbacks C2.
  Proof.
    intros z2 x2 y2 f2 g2.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x2)).
    { apply (isaprop_Pullback C2_univ). }
    intros [x1 ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y2)).
    { apply (isaprop_Pullback C2_univ). }
    intros [y1 iy].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw z2)).
    { apply (isaprop_Pullback C2_univ). }
    intros [z1 iz].

    induction (isotoid _ C2_univ ix).
    induction (isotoid _ C2_univ iy).
    induction (isotoid _ C2_univ iz).

    set (f1 := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ f2)).
    set (g1 := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ g2)).
    (* set (g1 := (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (iy · g2 · z_iso_inv iz))). *)

    (* assert (pf_f :  z_iso_inv ix · # F f1 · iz = f2). {
      unfold f1.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left.
      rewrite assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    }

    assert (pf_g :  z_iso_inv iy · # F g1 · iz = g2). {
      unfold g1.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left.
      rewrite assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    } *)

    set (t := weak_equiv_preserves_chosen_pullbacks Fw P1).
    unfold preserves_chosen_pullback in t.
    set (p := make_Pullback _ (t x1 y1 z1 f1 g1)).

    assert (pf_f : #F f1 = f2). {
      unfold f1 ; now rewrite functor_on_fully_faithful_inv_hom.
    }
    assert (pf_g : #F g1 = g2). {
      unfold g1 ; now rewrite functor_on_fully_faithful_inv_hom.
    }

    exact (pr1weq (transport_Pullback pf_f pf_g) p).
  Defined.

  Lemma weak_equiv_lifts_preserves_chosen_pullbacks_eq {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (P₁ : Pullbacks C1)
    (P₂ : Pullbacks (pr1 C2))
    (P₃ : Pullbacks (pr1 C3))
    (Gw : is_weak_equiv G)
    : preserves_chosen_pullbacks_eq F P₁ P₃
      → preserves_chosen_pullbacks_eq H P₂ P₃.
  Proof.
    intros Fpb x' y' z' f' g'.

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
    pose (ϕ₁ := nat_z_iso_pointwise_z_iso α x).
    pose (ϕ₂ := nat_z_iso_pointwise_z_iso α y).
    pose (ϕ₃ := z_iso_inv (nat_z_iso_pointwise_z_iso α z)).
    pose (ϕ₄ := nat_z_iso_pointwise_z_iso α (P₁ z x y f g)).
    pose (ψ := isotoid _ (pr2 C3) ϕ₄).
    refine (ψ @ _).
    refine (v @ _).
    use (isotoid _ (pr2 C3)).
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

  Definition cat_with_chosen_pullbacks_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw P1.
      exact (weak_equiv_preserves_pullbacks_univ C2_univ Fw (pr1 P1) ,, tt).
    - intros C P1.
      refine (tt ,, _).
      use weak_equiv_preserves_pullbacks_eq.
      + apply η_weak_equiv.
      + exact (pr2 (pr1 LUR C)).
    - intros C1 C2 C3 F G H α P1 P2 P3 Gw.
      intros [t Fprod].
      exists tt.
      exact (weak_equiv_lifts_preserves_chosen_pullbacks_eq C2 C3 α (pr1 P1) (pr1 P2) (pr1 P3) Gw Fprod).
  Defined.

End BicatOfCategoriesWithChosenPullbackHasRezkCompletion.
