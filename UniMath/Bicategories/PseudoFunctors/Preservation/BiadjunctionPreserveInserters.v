(******************************************************************

 Preservation of inserters by right biadjoints

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
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
Require Import UniMath.Bicategories.Limits.Inserters.

Local Open Scope cat.

Section BiadjunctionPreservation.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L).

  Section PreserveInsertersCommute.
    Context {y₁ y₂ : B₂}
            (f : y₁ --> y₂)
            (x : B₁).

    Definition inserter_commute_nat_trans_data
      : nat_trans_data
          (biadj_right_hom R x y₁ ∙ post_comp x (# R f))
          (post_comp (L x) f ∙ biadj_right_hom R x y₂)
      := λ h, rassociator _ _ _ • (_ ◃ psfunctor_comp R _ _).

    Definition inserter_commute_is_nat_trans
      : is_nat_trans
          _ _
          inserter_commute_nat_trans_data.
    Proof.
      intros h₁ h₂ α ; cbn.
      unfold inserter_commute_nat_trans_data.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      refine (!_).
      apply psfunctor_rwhisker.
    Qed.

    Definition inserter_commute_nat_trans
      : biadj_right_hom R x y₁ ∙ post_comp x (# R f)
        ⟹
        post_comp (L x) f ∙ biadj_right_hom R x y₂.
    Proof.
      use make_nat_trans.
      - exact inserter_commute_nat_trans_data.
      - exact inserter_commute_is_nat_trans.
    Defined.

    Definition inserter_commute_nat_z_iso
      : nat_z_iso
          (biadj_right_hom R x y₁ ∙ post_comp x (# R f))
          (post_comp (L x) f ∙ biadj_right_hom R x y₂).
    Proof.
      use make_nat_z_iso.
      - exact inserter_commute_nat_trans.
      - intro h.
        apply is_inv2cell_to_is_z_iso.
        cbn ; unfold inserter_commute_nat_trans_data.
        is_iso.
        apply property_from_invertible_2cell.
    Defined.
  End PreserveInsertersCommute.

  Section PreserveInserterNatIso.
    Context {y₁ y₂ : B₂}
            {f g : y₁ --> y₂}
            (i : inserter_cone f g)
            (x : B₁).

    Definition right_biadj_preserves_inserters_nat_trans_cell
               (h : x --> R i)
      : biadj_unit R x · # R (# L h · biadj_counit R i · inserter_cone_pr1 i)
        ==>
        h · # R (inserter_cone_pr1 i)
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
                 • invertible_modcomponent_of (biadj_triangle_r R) i) ▹ _)
                 • lunitor _)).

    Opaque psfunctor_comp.

    Local Notation "'lα'" := (lassociator _ _ _).
    Local Notation "'rα'" := (rassociator _ _ _).
    Local Notation "'lu'" := (lunitor _).
    Local Notation "'lui'" := (linvunitor _).
    Local Notation "'ru'" := (runitor _).
    Local Notation "'rui'" := (rinvunitor _).

    Definition right_biadj_preserves_inserters_nat_trans_path
               (h : x --> R i)
      : @dialgebra_mor_path
          _ _ _ _
          ((biadj_left_hom R x i
            ∙ inserter_cone_functor i (L x)
            ∙ dialgebra_equivalence_of_cats_functor
                (inserter_commute_nat_z_iso f x)
                (inserter_commute_nat_z_iso g x))
             h)
          (inserter_cone_functor (psfunctor_inserter_cone R i) x h)
          (right_biadj_preserves_inserters_nat_trans_cell h).
    Proof.
      unfold dialgebra_mor_path.
      cbn.
      unfold inserter_commute_nat_trans_data.
      unfold right_biadj_preserves_inserters_nat_trans_cell.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      do 3 refine (vassocl _ _ _ @ _).
      etrans.
      {
        do 3 apply maponpaths.
        admit.
        (*
        do 2 refine (vassocl _ _ _ @ _).
        do 3 apply maponpaths.
        do 6 refine (vassocl _ _ _ @ _).
        do 7 apply maponpaths.
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        apply vassocl.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply vassocl.
      }
      etrans.
      {
        do 5 apply maponpaths.
        apply id2_left.
      }
      do 7 refine (_ @ vassocr _ _ _).
      refine (!_).
      etrans.
      {
        do 7 apply maponpaths.
        do 2 refine (vassocl _ _ _ @ _).
        do 3 apply maponpaths.
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        do 2 refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      etrans.
      {
        do 8 apply maponpaths.
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (vassocl _ _ _ @ _) ; apply maponpaths.
        apply vassocl.
      }
      refine (!_).
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (!_).
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        apply rwhisker_lwhisker.
      }
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        apply rwhisker_lwhisker.
      }
      etrans.
      {
        apply maponpaths.
        apply vassocl.
      }
      use vcomp_move_R_pM ; [ is_iso | ].
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        cbn.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths ; apply maponpaths_2.
        cbn.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply rwhisker_vcomp.
        }
        etrans.
        {
          apply maponpaths.
          apply rwhisker_rwhisker_alt.
        }
        exact (!(rwhisker_vcomp _ _ _)).
      }
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply psfunctor_vcomp.
        }
        exact (!(lwhisker_vcomp _ _ _)).
      }
      etrans.
      {
        do 3 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          do 2 refine (vassocl _ _ _ @ _).
          apply maponpaths.
          refine (maponpaths (λ z, _ • z) (lwhisker_vcomp _ _ _) @ _).
          refine (lwhisker_vcomp _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (vassocr _ _ _ @ _).
            apply (psfunctor_rassociator R).
          }
          apply idpath.
        }
        refine (lwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (vassocr _ _ _ @ _).
            etrans.
            {
              apply maponpaths_2.
              apply rwhisker_rwhisker_alt.
            }
            refine (vassocl _ _ _ @ _).
            apply idpath.
          }
          refine (vassocl _ _ _ @ _).
          apply maponpaths.
          apply vassocl.
        }
        do 3 (refine (!(lwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
        apply idpath.
      }
      do 2 refine (vassocl _ _ _ @ _).
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        cbn.
        apply idpath.
      }
      etrans.
      {
        do 4 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply lassociator_lassociator.
        }
        do 2 refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_rwhisker.
        }
        refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply psfunctor_vcomp.
      }
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply rwhisker_lwhisker.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply rwhisker_lwhisker.
        }
        apply vassocl.
      }
      etrans.
      {
        do 5 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply pentagon_6.
        }
        do 2 refine (vassocl _ _ _ @ _).
        do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_rwhisker.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_rwhisker.
        }
        refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          do 4 refine (vassocr _ _ _ @ _).
          apply maponpaths_2.
          refine (maponpaths (λ z, ((z • _) • _) • _) (lwhisker_vcomp _ _ _) @ _).
          refine (maponpaths (λ z, (z • _) • _) (lwhisker_vcomp _ _ _) @ _).
          refine (maponpaths (λ z, z • _) (lwhisker_vcomp _ _ _) @ _).
          refine (lwhisker_vcomp _ _ _ @ _).
          apply maponpaths.
          do 4 refine (vassocl _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            do 3 apply maponpaths.
            apply rwhisker_rwhisker_alt.
          }
          do 3 refine (vassocr _ _ _ @ _).
          apply maponpaths_2.
          apply psfunctor_lassociator_alt'.
        }
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply vassocl.
      }
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (maponpaths (λ z, (_ • z) • _) (lwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, z • _) (lwhisker_vcomp _ _ _) @ _).
        refine (lwhisker_vcomp _ _ _ @ _).
        apply maponpaths.
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (vassocl _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            apply psfunctor_lwhisker.
          }
          refine (vassocl _ _ _ @ _).
          apply maponpaths.
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            apply vcomp_rinv.
          }
          apply id2_left.
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          refine (maponpaths (λ z, z • _) (vcomp_whisker _ _) @ _).
          refine (vassocl _ _ _ @ _).
          apply maponpaths.
          refine (vassocr _ _ _ @ _).
          refine (maponpaths (λ z, z • _) (vcomp_whisker _ _) @ _).
          refine (vassocl _ _ _ @ _).
          apply maponpaths.
          refine (vassocr _ _ _ @ _).
          refine (maponpaths (λ z, z • _) (vcomp_whisker _ _) @ _).
          refine (vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (rwhisker_vcomp _ _ _ @ _).
            refine (maponpaths (λ z, z ▹ _) (vcomp_rinv _) @ _).
            apply id2_rwhisker.
          }
          apply id2_right.
        }
        refine (maponpaths (λ z, _ • z) (lwhisker_vcomp _ _ _) @ _).
        apply lwhisker_vcomp.
      }
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply lwhisker_lwhisker.
      }
      refine (vassocl _ _ _ @ _ @ vassocr _ _ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        exact (!(vcomp_whisker _ _)).
      }
      refine (vassocl _ _ _ @ _).
      refine (_ @ vassocr _ _ _).
      apply maponpaths.
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        apply vcomp_whisker.
      }
      refine (vassocl _ _ _ @ _).
      refine (!_).
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, _ • (z ▹ _)) (!(rwhisker_rwhisker_alt _ _ _)) @ _).
        refine (maponpaths (λ z, _ • z) (!(rwhisker_vcomp _ _ _)) @ _).
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        apply vassocl.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply inverse_pentagon_7.
      }
      do 2 refine (vassocl _ _ _ @ _).
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        cbn.
        apply idpath.
      }
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        exact (!(lwhisker_lwhisker _ _ _)).
      }
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lassociator_lassociator _ _ _ _)).
        }
        do 2 refine (vassocl _ _ _ @ _).
        do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (rwhisker_vcomp _ _ _ @ _).
          refine (maponpaths (λ z, z ▹ _) (lassociator_rassociator _ _ _) @ _).
          apply id2_rwhisker.
        }
        apply id2_left.
      }
      etrans.
      {
        do 3 apply maponpaths.
        refine (maponpaths (λ z, _ • (_ • z)) (rwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
        refine (rwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          refine (maponpaths (λ z, _ • (_ • z)) (rwhisker_vcomp _ _ _) @ _).
          refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
          apply rwhisker_vcomp.
        }
        do 2 apply maponpaths.
        refine (maponpaths (λ z, _ • z) (lwhisker_vcomp _ _ _) @ _).
        apply lwhisker_vcomp.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        do 3 refine (vassocr _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (maponpaths (λ z, z • _) (rwhisker_vcomp _ _ _) @ _).
          apply rwhisker_vcomp.
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          refine (maponpaths (λ z, z • _) (lwhisker_vcomp _ _ _) @ _).
          apply lwhisker_vcomp.
        }
        etrans.
        {
          apply maponpaths_2.
          exact (!(rwhisker_lwhisker_rassociator _ _ _ _ _ _ _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        do 3 refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (maponpaths (λ z, (z • _) • _) (lwhisker_vcomp _ _ _) @ _).
          refine (maponpaths (λ z, z • _) (lwhisker_vcomp _ _ _) @ _).
          apply lwhisker_vcomp.
        }
        apply maponpaths_2.
        apply maponpaths.
        do 2 refine (vassocl _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!(rwhisker_vcomp _ _ _) @ maponpaths (λ z, z • _) _).
          do 3 (refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
          exact (!(rwhisker_vcomp _ _ _)).
        }
        do 2 refine (vassocl _ _ _ @ _) ; apply maponpaths.
        do 2 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
        apply vassocl.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (maponpaths (λ z, z • _) (lwhisker_hcomp _ _) @ _).
          apply pentagon_2.
        }
        etrans.
        {
          apply maponpaths_2.
          do 2 apply maponpaths.
          exact (!(rwhisker_hcomp _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        apply rwhisker_vcomp.
      }
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply lwhisker_lwhisker.
      }
      refine (vassocl _ _ _ @ _).
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        cbn.
        apply idpath.
      }
      do 2 refine (vassocr _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (!(inverse_pentagon_7 _  _ _ _)).
      }
      refine (vassocl _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          do 2 (refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
          etrans.
          {
            apply maponpaths.
            refine (!(lwhisker_vcomp _ _ _) @ _) ; apply maponpaths.
            exact (!(lwhisker_vcomp _ _ _)).
          }
          refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths.
          exact (!(rwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          do 4 apply maponpaths.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              do 2 (refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
              exact (!(rwhisker_vcomp _ _ _)).
            }
            do 2 (refine (!(lwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
            exact (!(lwhisker_vcomp _ _ _)).
          }
          do 2 (refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
          exact (!(rwhisker_vcomp _ _ _)).
        }
        do 4 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        do 3 refine (vassocr _ _ _ @ _).
        do 5 apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, _ • (z ▹ _)) (!(rassociator_rassociator _ _ _ _)) @ _).
        etrans.
        {
          apply maponpaths.
          refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths_2.
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (vassocr _ _ _) @ _).
        refine (maponpaths (λ z, (z • _) • _) (rwhisker_rwhisker _ _ _) @ _).
        refine (vassocl _ _ _ @ _).
        cbn.
        apply idpath.
      }
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          do 7 refine (vassocl _ _ _ @ _) ; do 2 apply maponpaths.
          apply vassocl.
        }
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (!(vcomp_whisker _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (rwhisker_vcomp _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              apply rassociator_lassociator.
            }
            apply lwhisker_id2.
          }
          apply id2_rwhisker.
        }
        apply id2_left.
      }
      etrans.
      {
        apply maponpaths.
        refine (vassocl _ _ _ @ _) ; do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (rwhisker_vcomp _ _ _ @ _).
        apply maponpaths.
        cbn.
        apply rwhisker_lwhisker_rassociator.
      }
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (maponpaths (λ z, _ • z) (vassocl _ _ _) @ _).
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        apply rwhisker_rwhisker.
      }
      etrans.
      {
        apply maponpaths.
        refine (maponpaths (λ z, _ • z) (vassocl _ _ _) @ _).
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        exact (!(vcomp_whisker _ _)).
      }
      refine (maponpaths (λ z, _ • z) (vassocl _ _ _) @ _).
      etrans.
      {
        do 4 apply maponpaths.
        do 3 refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, ((z • _) • _) • _) (rwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, (z • _) • _) (rwhisker_vcomp _ _ _) @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_vcomp _ _ _) @ _).
        refine (rwhisker_vcomp _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          do 3 apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        do 3 refine (vassocl _ _ _ @ _).
        apply maponpaths.
        do 2 refine (vassocr _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        do 2 refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        apply vassocl.
      }
      etrans.
      {
        do 3 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          do 3 (refine (!(rwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        apply vassocl.
      }
      etrans.
      {
        do 2 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (!(vcomp_whisker _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          do 3 apply maponpaths.
          refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
          do 2 apply maponpaths.
          apply lunitor_lwhisker.
        }
        do 3 apply maponpaths.
        apply rwhisker_rwhisker.
      }
      do 6 refine (vassocr _ _ _ @ _).
      do 4 refine (_ @ vassocl _ _ _).
      apply maponpaths_2.
      do 5 refine (vassocl _ _ _ @ _).
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (!(vcomp_whisker _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (!(vcomp_whisker _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        exact (maponpaths (λ z, _ • z) (!(vcomp_whisker _ _))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        do 5 (refine (!(lwhisker_vcomp _ _ _) @ _) ; apply maponpaths).
        exact (!(lwhisker_vcomp _ _ _)).
      }
      do 5 refine (_ @ vassocl _ _ _).
      do 6 refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      do 8 refine (vassocl _ _ _ @ _).
      do 4 refine (_ @ vassocr _ _ _).
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        apply rwhisker_vcomp.
      }
      refine (!_).
      etrans.
      {
        do 8 apply maponpaths.
        refine (lwhisker_vcomp _ _ _ @ _).
        apply maponpaths.
        apply rwhisker_vcomp.
      }
      etrans.
      {
        do 3 apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply rwhisker_lwhisker_rassociator.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(lwhisker_vcomp _ _ _)).
          }
          exact (!(rwhisker_vcomp _ _ _)).
        }
        apply vassocl.
      }
      do 8 refine (vassocr _ _ _ @ _).
      use vcomp_move_R_Mp ; [ is_iso | ].
      do 7 refine (vassocl _ _ _ @ _).
      refine (!_).
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 2 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
        apply vassocl.
      }
      etrans.
      {
        do 5 apply maponpaths.
        cbn.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        refine (maponpaths (λ z, z • _) (!(rwhisker_vcomp _ _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (!(rwhisker_rwhisker _ _ _)) @ _).
        pose (maponpaths
                (λ z, rassociator _ _ _ • z)
                (runitor_rwhisker h (# R (inserter_cone_pr1 i))))
          as p.
        cbn in p.
        rewrite !vassocr in p.
        rewrite rassociator_lassociator, id2_left in p.
        etrans.
        {
          do 3 apply maponpaths.
          exact p.
        }
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (!(rwhisker_rwhisker _ _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (maponpaths (λ z, _ • z) (!(rwhisker_vcomp _ _ _)) @ _).
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_vcomp _ _ _) @ _).
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          refine (!_).
          apply rwhisker_lwhisker_rassociator.
        }
        exact (maponpaths (λ z, z • _) (!(rwhisker_vcomp _ _ _))).
      }
      do 5 refine (vassocr _ _ _ @ _).
      do 7 refine (_ @ vassocl _ _ _).
      apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      do 4 refine (vassocl _ _ _ @ _).
      do 5 refine (_ @ vassocr _ _ _).
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        do 2 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (maponpaths (λ z, z • _) (rwhisker_vcomp _ _ _) @ _).
        refine (rwhisker_vcomp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (maponpaths (λ z, z • _) (!(rassociator_rassociator _ _ _ _)) @ _).
          refine (vassocl _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (lwhisker_vcomp _ _ _ @ _).
            refine (maponpaths (λ z, _ ◃ z) (rassociator_lassociator _ _ _) @ _).
            apply lwhisker_id2.
          }
          apply id2_right.
        }
        exact (!(rwhisker_vcomp _ _ _)).
      }
      etrans.
      {
        refine (maponpaths (λ z, _ • z) (vassocl _ _ _) @ _).
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        do 2 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (maponpaths (λ z, _ • z) (!(rwhisker_vcomp _ _ _)) @ _).
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        apply vassocl.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        do 2 refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        refine (maponpaths (λ z, _ • z) (rwhisker_vcomp _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          apply rwhisker_lwhisker_rassociator.
        }
        refine (maponpaths (λ z, _ • z) (!(rwhisker_vcomp _ _ _)) @ _).
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (rwhisker_rwhisker _ _ _) @ _).
        apply vassocl.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        refine (vassocr _ _ _ @ _).
        refine (maponpaths (λ z, z • _) (!(rwhisker_rwhisker _ _ _)) @ _).
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (rwhisker_vcomp _ _ _ @ !_).
        apply maponpaths.
        apply rwhisker_lwhisker_rassociator.
      }
      refine (_ @ vassocr _ _ _).
      apply maponpaths.
      refine (!_).
      apply rwhisker_vcomp.
    Qed. *)
Admitted.

    Transparent psfunctor_comp.

    Definition right_biadj_preserves_inserters_nat_trans_data
      : nat_trans_data
          (biadj_left_hom R x i
           ∙ inserter_cone_functor i (L x)
           ∙ dialgebra_equivalence_of_cats_functor
               (inserter_commute_nat_z_iso f x)
               (inserter_commute_nat_z_iso g x))
          (inserter_cone_functor (psfunctor_inserter_cone R i) x).
    Proof.
      intro h.
      use make_dialgebra_mor.
      - exact (right_biadj_preserves_inserters_nat_trans_cell h).
      - exact (right_biadj_preserves_inserters_nat_trans_path h).
    Defined.

    Definition right_biadj_preserves_inserters_is_nat_trans
      : is_nat_trans
          _ _
          right_biadj_preserves_inserters_nat_trans_data.
    Proof.
      intros h₁ h₂ α.
      use eq_dialgebra.
      cbn.
      unfold right_biadj_preserves_inserters_nat_trans_cell.
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
          assert (## R ((## L α ▹ biadj_counit R i) ▹ inserter_cone_pr1 i)
                  • (psfunctor_comp R _ _)^-1
                  =
                  (psfunctor_comp R _ _)^-1
                  • (## R (## L α ▹ biadj_counit R i) ▹ # R (inserter_cone_pr1 i)))
            as H.
          {
            use vcomp_move_R_Mp ; [ is_iso | ].
            rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            exact (psfunctor_rwhisker
                     R
                     (inserter_cone_pr1 i)
                     (## L α ▹ biadj_counit R i)).
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
          assert (## R (## L α ▹ biadj_counit R i)
                  • ( psfunctor_comp R _ _)^-1
                  =
                  (psfunctor_comp R _ _)^-1
                  • (## R (## L α) ▹ # R (biadj_counit R i)))
            as H.
          {
            use vcomp_move_R_Mp ; [ is_iso | ].
            rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            exact (psfunctor_rwhisker R (biadj_counit R i) (##L α)).
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
            exact (psnaturality_natural (biadj_unit R) _ _ _ _ α).
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

    Definition right_biadj_preserves_inserters_nat_trans
      : biadj_left_hom R x i
        ∙ inserter_cone_functor i (L x)
        ∙ dialgebra_equivalence_of_cats_functor
            (inserter_commute_nat_z_iso f x)
            (inserter_commute_nat_z_iso g x)
        ⟹
        inserter_cone_functor (psfunctor_inserter_cone R i) x.
    Proof.
      use make_nat_trans.
      - exact right_biadj_preserves_inserters_nat_trans_data.
      - exact right_biadj_preserves_inserters_is_nat_trans.
    Defined.

    Definition right_biadj_preserves_inserters_is_nat_z_iso
      : is_nat_z_iso right_biadj_preserves_inserters_nat_trans.
    Proof.
      intro h.
      use is_z_iso_dialgebra.
      use is_inv2cell_to_is_z_iso.
      cbn ; unfold right_biadj_preserves_inserters_nat_trans_cell.
      is_iso.
      - apply property_from_invertible_2cell.
      - apply property_from_invertible_2cell.
    Defined.
  End PreserveInserterNatIso.

  Definition right_biadj_preserves_inserters
             (HB₁ : is_univalent_2_1 B₁)
             (HB₂ : is_univalent_2_1 B₂)
    : preserves_inserters R.
  Proof.
    intros y₁ y₂ f g i Hi.
    use universal_inserter_cone_has_ump.
    intro x.
    use nat_iso_adj_equivalence_of_cats.
    - refine (biadj_left_hom R x i
              ∙ inserter_cone_functor i (L x)
              ∙ _).
      use dialgebra_equivalence_of_cats_functor.
      + exact (biadj_right_hom R x y₁).
      + exact (biadj_right_hom R x y₂).
      + exact (inserter_commute_nat_z_iso f x).
      + exact (inserter_commute_nat_z_iso g x).
    - exact (right_biadj_preserves_inserters_nat_trans i x).
    - exact (right_biadj_preserves_inserters_is_nat_z_iso i x).
    - use comp_adj_equivalence_of_cats.
      + use comp_adj_equivalence_of_cats.
        * exact (biadj_hom_equiv R x i).
        * apply (make_is_universal_inserter_cone HB₂ _ Hi).
      + use dialgebra_adj_equivalence_of_cats.
        * exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y₁)).
        * exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R x y₂)).
  Defined.
End BiadjunctionPreservation.
