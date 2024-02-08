(*
In this file, we show how the Rezk completion of a categories has a suitable binary products (in terms of preservation) if the original category has binary products.
Hence, categories with binary products admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithBinProductsHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with binary products (up to propositional truncation).
2. BicatOfCategoriesWithChosenBinProductsHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with chosen binary products.
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

Require Import UniMath.CategoryTheory.WeakEquivalences.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

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

Section BicatOfCategoriesWithBinProductsHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_have_binproducts.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_have_binproducts)).

  Definition cat_with_binproducts_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw BP₁.
      refine (_ ,, tt).
      intros y1 y2.

      use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y1)).
      { apply propproperty. }
      intros [x1 i1].
      use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y2)).
      { apply propproperty. }
      intros [x2 i2].

      use (factor_through_squash _ _ (pr1 BP₁ x1 x2)).
      { apply propproperty. }
      intro p.
      apply hinhpr.
      simpl in BP₁.
      set (t := weak_equiv_preserves_binproducts Fw _ _ _ _ _ (pr2 p)).
      pose (PB := make_BinProduct _ _ _ _ _ _ t).
      exact (binproduct_of_isos PB i1 i2).
    - intros C BP.
      refine (tt ,, _).
      apply weak_equiv_preserves_binproducts.
      apply η_weak_equiv.
    - intros C1 C2 C3 F G H α C1_prod C2_prod C3_prod Gw.
      simpl.
      intros [t Fprod].
      exists tt.
      intros y1 y2 py π₁p π₂p p_ispr.

      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
      { apply isaprop_isBinProduct. }
      intros [x1 i1].
      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
      { apply isaprop_isBinProduct. }
      intros [x2 i2].
      simpl in C1_prod, C2_prod, C3_prod.

      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw py)).
      { apply isaprop_isBinProduct. }
      intros [px i].

      set (G_reflect := weak_equiv_reflects_products (ff_from_weak_equiv _ Gw) x1 x2 px).
      set (π₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₁p · z_iso_inv i1)).
      set (π₂ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₂p · z_iso_inv i2)).

      set (is1 := z_iso_comp (functor_on_z_iso H (z_iso_inv i1)) ((_,, pr2 α x1))).
      set (is2 := z_iso_comp (functor_on_z_iso H (z_iso_inv i2)) ((_,, pr2 α x2))).

      assert (pf1 :  i · π₁p = # G π₁ · i1).
      {
        unfold π₁.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite assoc'.
        rewrite z_iso_inv_after_z_iso.
        now rewrite id_right.
      }

      assert (pf2 :  i · π₂p = # G π₂ · i2).
      {
        unfold π₂.
        rewrite functor_on_fully_faithful_inv_hom.
        rewrite assoc'.
        rewrite z_iso_inv_after_z_iso.
        now rewrite id_right.
      }

      use (isbinproduct_of_isos _ is1 is2).
      + use (make_BinProduct _ _ _ _ _ _ (Fprod _ _ _ _ _ (G_reflect π₁ π₂ _))).
        exact (isbinproduct_of_isos (make_BinProduct _ _ _ _ _ _ p_ispr) i1 i2 i _ _ pf1 pf2).
      + exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i)) (_ ,, pr2 α px)).
      + simpl.
        rewrite assoc'.
        etrans. {
          apply maponpaths.
          exact (! pr21 α _ _ π₁).
        }
        simpl.
        rewrite ! assoc.
        rewrite <- ! functor_comp.
        apply maponpaths_2, maponpaths.
        use z_iso_inv_on_left.
        rewrite assoc'.
        rewrite <- pf1.
        rewrite assoc.
        rewrite z_iso_after_z_iso_inv.
        now rewrite ! id_left.
      + simpl.
        rewrite assoc'.
        etrans. {
          apply maponpaths.
          exact (! pr21 α _ _ π₂).
        }
        simpl.
        rewrite ! assoc.
        rewrite <- ! functor_comp.
        apply maponpaths_2, maponpaths.
        use z_iso_inv_on_left.
        rewrite assoc'.
        rewrite <- pf2.
        rewrite assoc.
        rewrite z_iso_after_z_iso_inv.
        now rewrite ! id_left.
  Defined.

End BicatOfCategoriesWithBinProductsHasRezkCompletion.

Section BicatOfCategoriesWithChosenBinproductsHasRezkCompletion.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.
  Context (LUR : left_universal_arrow R).
  Let η := (pr12 LUR).
  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).

  Let D := disp_bicat_chosen_binproducts.

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_chosen_binproducts)).

  Section A.

    Context {C1 C2 : category}
      (C2_univ : is_univalent C2)
      {F : C1 ⟶ C2}
      (Fw : is_weak_equiv F)
      (C1_prod : BinProducts C1).

    Definition C2_prod : BinProducts C2.
    Proof.
      intros x2 y2.
      use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x2)).
      { apply (isaprop_BinProduct C2_univ). }
      intros [x1 ix].
      use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y2)).
      { apply (isaprop_BinProduct C2_univ). }
      intros [y1 iy].

      use (binproduct_of_isos _ ix iy).

      set (t := weak_equiv_preserves_chosen_binproducts Fw C1_prod).
      exact (make_BinProduct _ _ _ _ _ _ (t x1 y1)).
    Defined.

  End A.

  Definition cat_with_chosen_binproducts_has_RezkCompletion
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact η_weak_equiv.
    - intros C1 C2 C2_univ F Fw C1_prod.
      exact (C2_prod C2_univ Fw (pr1 C1_prod) ,, tt).
    - intros C C1_prod.
      refine (tt ,, _).
      use weak_equiv_preserves_binproducts_eq.
      + apply η_weak_equiv.
      + exact (pr2 (pr1 LUR C)).
    - intros C1 C2 C3 F G H α C1_prod C2_prod C3_prod Gw.
      intros [t Fprod].
      exists tt.

      intros y1 y2.
      (*simpl.
      simpl in Fprod.*)

      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
      { apply isapropishinh. }
      intros [x1 i1].

      use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
      { apply isapropishinh. }
      intros [x2 i2].

      unfold preserves_chosen_binproducts_eq in Fprod.

      use (factor_through_squash _ _ (Fprod x1 x2)).
      { apply isapropishinh. }
      intro p.

      pose (ϕ₁ := nat_z_iso_pointwise_z_iso α x1).
      pose (ϕ₂ := nat_z_iso_pointwise_z_iso α x2).
      pose (ϕ₃ := nat_z_iso_pointwise_z_iso α (pr1 C1_prod x1 x2)).

      pose (ψ₁ := isotoid _ (pr2 C3) ϕ₁).
      pose (ψ₂ := isotoid _ (pr2 C3) ϕ₂).
      pose (ψ₃ := isotoid _ (pr2 C3) ϕ₃).

      pose (j1 := isotoid _ (pr2 C2) i1).
      pose (j2 := isotoid _ (pr2 C2) i2).

      (*
        H (y1 × y2) = H (G x1 × G x2)
          = H (G (x1 × x2))
          = F (x1 × x2)
          = F x1 × F x2
          = H(G(x1)) × H(G(x2))
          = H y1 × H y2.

       *)


      set (Gprod := weak_equiv_preserves_binproducts_eq Gw (pr2 C2) (pr1 C1_prod) (pr1 C2_prod)).
      use (factor_through_squash _ _ (Gprod x1 x2)).
      { apply isapropishinh. }
      intro Gx1x2.
      clear Gprod.

      apply hinhpr.

      rewrite <- j1, <- j2.
      etrans. {
        apply maponpaths.
        exact (! Gx1x2).
      }

      refine (ψ₃ @ _).
      refine (p @ _).

      refine (maponpaths (fun z => BinProductObject _ (pr1 C3_prod z _)) _ @ _).
      { exact (! ψ₁). }
      refine (maponpaths (fun z => BinProductObject _ (pr1 C3_prod _ z)) _).
      exact (! ψ₂).

  Defined.

End BicatOfCategoriesWithChosenBinproductsHasRezkCompletion.
