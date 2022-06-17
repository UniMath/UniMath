(******************************************************************

 Preservation of equifiers by right biadjoints

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.FullEquivalences.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

Section BiadjunctionPreservation.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L).

  Section PreserveEquifiers.
    Context {y₁ y₂ : B₂}
            {f g : y₁ --> y₂}
            {α β : f ==> g}
            {e : equifier_cone f g α β}
            (He : has_equifier_ump e).

    Definition preserve_equifiers_R_path
               {x : B₁}
               (h : L x --> y₁)
               (p : h ◃ α = h ◃ β)
      : biadj_unit R x · # R h ◃ ## R α
        =
        biadj_unit R x · # R h ◃ ## R β.
    Proof.
      pose (maponpaths
              (λ z, psfunctor_comp _ _ _ • ##R z)
              p)
        as q.
      cbn -[psfunctor_comp] in q.
      rewrite !psfunctor_lwhisker in q.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- !lwhisker_lwhisker.
      apply maponpaths_2.
      apply maponpaths.
      use (vcomp_rcancel (psfunctor_comp R h g)).
      {
        apply property_from_invertible_2cell.
      }
      exact q.
    Qed.

    Definition right_biadj_preserves_equifiers_nat_trans_cell
               {x : B₁}
               (h : x --> R e)
      : biadj_unit R x · # R (# L h · biadj_counit R e · equifier_cone_pr1 e)
        ==>
        h · # R (equifier_cone_pr1 e)
      := (_ ◃ ((psfunctor_comp R _ _)^-1
               • ((psfunctor_comp R _ _)^-1 ▹ _)))
         • lassociator _ _ _
         • (lassociator _ _ _ ▹ _)
         • (((psnaturality_of (biadj_unit R) h) ▹ _) ▹ _)
         • rassociator _ _ _
         • rassociator _ _ _
         • (_ ◃ (lassociator _ _ _
                 • ((linvunitor _
                 • (_ ◃ (_ ◃ (linvunitor _ • (_ ◃ rinvunitor _))))
                 • invertible_modcomponent_of (biadj_triangle_r R) e) ▹ _)
                 • lunitor _)).

    Definition right_biadj_preserves_equifiers_commute_data
               (x : B₁)
      : nat_trans_data
          (biadj_left_hom R x e
           ∙ to_universal_equifier_cat e (L x)
           ∙ full_sub_category_functor
               (λ (h : hom (L x) y₁),
                make_hProp
                  (h ◃ α = h ◃ β)
                  (cellset_property _ _ _ _))
               (λ (h : hom x (R y₁)),
                make_hProp
                  (h ◃ ## R α = h ◃ ## R β)
                  (cellset_property _ _ _ _))
               (biadj_right_hom R x y₁)
               preserve_equifiers_R_path)
          (to_universal_equifier_cat (psfunctor_equifier_cone R e) x)
      := λ h, right_biadj_preserves_equifiers_nat_trans_cell h ,, tt.

    Definition right_biadj_preserves_equifiers_commute_is_nat_trans
               (x : B₁)
      : is_nat_trans
          _ _
          (right_biadj_preserves_equifiers_commute_data x).
    Proof.
      intros h₁ h₂ ζ.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      cbn.
      unfold right_biadj_preserves_equifiers_nat_trans_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        rewrite lwhisker_vcomp.
        etrans.
        {
          apply maponpaths.
          assert (## R ((## L ζ ▹ biadj_counit R e) ▹ equifier_cone_pr1 e)
                  • (psfunctor_comp R _ _)^-1
                  =
                  (psfunctor_comp R _ _)^-1
                  • (## R (## L ζ ▹ biadj_counit R e) ▹ # R (equifier_cone_pr1 e)))
            as H.
          {
            use vcomp_move_R_Mp ; [ is_iso | ].
            rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            exact (psfunctor_rwhisker
                     R
                     (equifier_cone_pr1 e)
                     (## L ζ ▹ biadj_counit R e)).
          }
          exact H.
        }
        rewrite <- lwhisker_vcomp.
        apply idpath.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        rewrite lwhisker_vcomp.
        rewrite rwhisker_vcomp.
        etrans.
        {
          do 2 apply maponpaths.
          assert (## R (## L ζ ▹ biadj_counit R e)
                  • ( psfunctor_comp R _ _)^-1
                  =
                  (psfunctor_comp R _ _)^-1
                  • (## R (## L ζ) ▹ # R (biadj_counit R e)))
            as H.
          {
            use vcomp_move_R_Mp ; [ is_iso | ].
            rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            exact (psfunctor_rwhisker R (biadj_counit R e) (##L ζ)).
          }
          exact H.
        }
        rewrite <- rwhisker_vcomp.
        rewrite <- lwhisker_vcomp.
        apply idpath.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply rwhisker_lwhisker.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (rwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply rwhisker_lwhisker.
        }
        exact (!(rwhisker_vcomp _ _ _)).
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (rwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (rwhisker_vcomp _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            exact (psnaturality_natural (biadj_unit R) _ _ _ _ ζ).
          }
          cbn.
          exact (!(rwhisker_vcomp _ _ _)).
        }
        exact (!(rwhisker_vcomp _ _ _)).
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply rwhisker_rwhisker_alt.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply rwhisker_rwhisker_alt.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply vcomp_whisker.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply vcomp_whisker.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply vcomp_whisker.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply vcomp_whisker.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      apply vcomp_whisker.
    Qed.

    Definition right_biadj_preserves_equifiers_commute
               (x : B₁)
      : biadj_left_hom R x e
        ∙ to_universal_equifier_cat e (L x)
        ∙ full_sub_category_functor
            (λ (h : hom (L x) y₁),
             make_hProp
               (h ◃ α = h ◃ β)
               (cellset_property _ _ _ _))
            (λ (h : hom x (R y₁)),
             make_hProp
               (h ◃ ## R α = h ◃ ## R β)
               (cellset_property _ _ _ _))
            (biadj_right_hom R x y₁)
            preserve_equifiers_R_path
        ⟹
        to_universal_equifier_cat (psfunctor_equifier_cone R e) x.
    Proof.
      use make_nat_trans.
      - exact (right_biadj_preserves_equifiers_commute_data x).
      - exact (right_biadj_preserves_equifiers_commute_is_nat_trans x).
    Defined.

    Definition right_biadj_preserves_equifiers_commute_is_nat_iso
               (x : B₁)
      : is_nat_iso (right_biadj_preserves_equifiers_commute x).
    Proof.
      intro h.
      use is_iso_full_sub.
      use is_inv2cell_to_is_iso.
      cbn.
      unfold right_biadj_preserves_equifiers_nat_trans_cell.
      is_iso.
      - apply property_from_invertible_2cell.
      - apply property_from_invertible_2cell.
    Defined.

    Definition preserve_equifiers_L_path
               {x : B₁}
               (h : x --> R y₁)
               (p : h ◃ ## R α = h ◃ ## R β)
      : # L h · biadj_counit R y₁ ◃ α
        =
        # L h · biadj_counit R y₁ ◃ β.
    Proof.
      pose (maponpaths
              (λ z, psfunctor_comp _ _ _ • ##L z • (psfunctor_comp _ _ _)^-1)
              p)
        as q.
      cbn -[psfunctor_comp] in q.
      rewrite !psfunctor_lwhisker in q.
      rewrite !vassocl in q.
      rewrite !vcomp_rinv in q.
      rewrite !id2_right in q.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- !lwhisker_lwhisker.
      apply maponpaths_2.
      use (vcomp_rcancel (_ ◃ psnaturality_of (biadj_counit R) g)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      rewrite !lwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        exact (psnaturality_natural (biadj_counit R) _ _ _ _ α).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (psnaturality_natural (biadj_counit R) _ _ _ _ β).
      }
      refine (!_).
      cbn.
      rewrite <- !lwhisker_vcomp.
      apply maponpaths.
      use (vcomp_rcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !rwhisker_lwhisker.
      do 2 apply maponpaths.
      exact q.
    Qed.
  End PreserveEquifiers.

  Definition right_biadj_preserves_equifiers
             (HB₁ : is_univalent_2_1 B₁)
             (HB₂ : is_univalent_2_1 B₂)
    : preserves_equifiers R.
  Proof.
    intros y₁ y₂ f g α β e He.
    use universal_equifier_cone_has_ump.
    intro x.
    use nat_iso_adj_equivalence_of_cats.
    - exact (biadj_left_hom R x e
             ∙ to_universal_equifier_cat e (L x)
             ∙ full_sub_category_functor
                 (λ (h : hom (L x) y₁),
                  make_hProp
                    (h ◃ α = h ◃ β)
                    (cellset_property _ _ _ _))
                 (λ (h : hom x (R y₁)),
                  make_hProp
                    (h ◃ ## R α = h ◃ ## R β)
                    (cellset_property _ _ _ _))
                 (biadj_right_hom R x y₁)
                 preserve_equifiers_R_path).
    - exact (right_biadj_preserves_equifiers_commute x).
    - exact (right_biadj_preserves_equifiers_commute_is_nat_iso x).
    - use comp_adj_equivalence_of_cats.
      + use comp_adj_equivalence_of_cats.
        * exact (biadj_hom_equiv R x e).
        * apply (make_is_universal_equifier_cone HB₂ _ He).
      + use full_sub_category_adj_equivalence.
        * exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y₁)).
        * exact preserve_equifiers_L_path.
  Defined.
End BiadjunctionPreservation.
