(******************************************************************

 Preservation of coproducts by left biadjoints

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

Section BiadjunctionPreservation.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L).

  Definition left_biadj_preserves_binprods_1cell
             (x : B₂)
             {y₁ y₂ : B₁}
             (p : bincoprod_cocone y₁ y₂)
    : hom (psfunctor_bincoprod_cocone L p) x
      ⟶
      category_binproduct (hom (L y₁) x) (hom (L y₂) x)
    := biadj_right_hom R p x
       ∙ universal_coprod_functor p (R x)
       ∙ pair_functor
           (biadj_left_hom R y₁ x)
           (biadj_left_hom R y₂ x).

  Definition left_biadj_preserves_binprods_1cell_adj_equiv
             (HB₁ : is_univalent_2_1 B₁)
             (x : B₂)
             {y₁ y₂ : B₁}
             (p : bincoprod_cocone y₁ y₂)
             (Hp : has_bincoprod_ump p)
    : adj_equivalence_of_cats (left_biadj_preserves_binprods_1cell x p).
  Proof.
    use comp_adj_equivalence_of_cats.
    - use comp_adj_equivalence_of_cats.
      + exact (adj_equivalence_of_cats_inv (biadj_hom_equiv R p x)).
      + apply (make_is_universal_coprod_cocone HB₁ _ Hp).
    - use pair_adj_equivalence_of_cats.
      + exact (biadj_hom_equiv R y₁ x).
      + exact (biadj_hom_equiv R y₂ x).
  Defined.

  Section PreserveCoproducts.
    Context {y₁ y₂ : B₁}
            (p : bincoprod_cocone y₁ y₂)
            (x : B₂).

    Definition left_biadj_preserves_bincoprod_nat_trans_data
      : nat_trans_data
          (left_biadj_preserves_binprods_1cell x p)
          (universal_coprod_functor (psfunctor_bincoprod_cocone L p) x).
    Proof.
      intro f.
      simple refine (_ ,, _) ; cbn ; cbn in f.
      - refine (((psfunctor_comp L _ _)^-1 ▹ _)
                • rassociator _ _ _
                • (_ ◃ (((psfunctor_comp L _ _)^-1 ▹ _)
                        • rassociator _ _ _
                        • (_ ◃ psnaturality_of (biadj_counit R) f^-1)
                        • lassociator _ _ _
                        • ((linvunitor _ •  _) ▹ _)
                        • lunitor _))).
        exact ((_ ◃ (_ ◃ (linvunitor _ • (_ ◃ rinvunitor _))))
               • invertible_modcomponent_of (biadj_triangle_l R) p).
      - refine (((psfunctor_comp L _ _)^-1 ▹ _)
                • rassociator _ _ _
                • (_ ◃ (((psfunctor_comp L _ _)^-1 ▹ _)
                        • rassociator _ _ _
                        • (_ ◃ psnaturality_of (biadj_counit R) f^-1)
                        • lassociator _ _ _
                        • ((linvunitor _ •  _) ▹ _)
                        • lunitor _))).
        exact ((_ ◃ (_ ◃ (linvunitor _ • (_ ◃ rinvunitor _))))
               • invertible_modcomponent_of (biadj_triangle_l R) p).
    Defined.

    Opaque psfunctor_comp.

    Definition left_biadj_preserves_bincoprod_is_nat_trans
      : is_nat_trans _ _ left_biadj_preserves_bincoprod_nat_trans_data.
    Proof.
      intros f₁ f₂ α.
      use pathsdirprod.
      - simpl.
        refine (vassocr _ _ _ @ _ @ vassocr _ _ _).
        rewrite !vassocl.
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          apply maponpaths_2.
          rewrite rwhisker_vcomp.
          etrans.
          {
            apply maponpaths.
            pose (maponpaths
                    (λ z, (psfunctor_comp L _ _)^-1 • z • (psfunctor_comp L _ _)^-1)
                    (psfunctor_lwhisker
                       L
                       (bincoprod_cocone_inl p)
                       (biadj_unit R p ◃ ## R α)))
              as q.
            cbn in q.
            rewrite !vassocl in q.
            rewrite vcomp_rinv in q.
            rewrite id2_right in q.
            rewrite !vassocr in q.
            rewrite vcomp_linv in q.
            rewrite id2_left in q.
            exact q.
          }
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply rwhisker_lwhisker_rassociator.
          }
          apply vassocl.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply lwhisker_vcomp.
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (rwhisker_vcomp _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                pose (maponpaths
                        (λ z, (psfunctor_comp _ _ _)^-1 • z • (psfunctor_comp _ _ _)^-1)
                        (psfunctor_lwhisker L (biadj_unit R p) (##R α)))
                  as q.
                cbn in q.
                rewrite !vassocl in q.
                rewrite vcomp_rinv in q.
                rewrite id2_right in q.
                rewrite !vassocr in q.
                rewrite vcomp_linv in q.
                rewrite id2_left in q.
                exact q.
              }
              exact (!(rwhisker_vcomp _ _ _)).
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply rwhisker_lwhisker_rassociator.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (lwhisker_vcomp _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                pose (maponpaths
                        (λ z, (psnaturality_of (biadj_counit R) _)^-1
                              • z
                              • (psnaturality_of (biadj_counit R) _)^-1)
                        (psnaturality_natural (biadj_counit R) _ _ _ _ α))
                  as q.
                cbn in q.
                rewrite !vassocl in q.
                rewrite vcomp_rinv in q.
                rewrite id2_right in q.
                rewrite !vassocr in q.
                rewrite vcomp_linv in q.
                rewrite id2_left in q.
                exact (!q).
              }
              exact (!(lwhisker_vcomp _ _ _)).
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              apply lwhisker_lwhisker.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            rewrite lwhisker_vcomp.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply vcomp_whisker.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (lwhisker_vcomp _ _ _ @ _ @ !(lwhisker_vcomp _ _ _)).
        apply maponpaths.
        refine (!_).
        apply vcomp_lunitor.
      - simpl.
        refine (vassocr _ _ _ @ _ @ vassocr _ _ _).
        rewrite !vassocl.
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          apply maponpaths_2.
          rewrite rwhisker_vcomp.
          etrans.
          {
            apply maponpaths.
            pose (maponpaths
                    (λ z, (psfunctor_comp L _ _)^-1 • z • (psfunctor_comp L _ _)^-1)
                    (psfunctor_lwhisker
                       L
                       (bincoprod_cocone_inr p)
                       (biadj_unit R p ◃ ## R α)))
              as q.
            cbn in q.
            rewrite !vassocl in q.
            rewrite vcomp_rinv in q.
            rewrite id2_right in q.
            rewrite !vassocr in q.
            rewrite vcomp_linv in q.
            rewrite id2_left in q.
            exact q.
          }
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply rwhisker_lwhisker_rassociator.
          }
          apply vassocl.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply lwhisker_vcomp.
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (rwhisker_vcomp _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                pose (maponpaths
                        (λ z, (psfunctor_comp _ _ _)^-1 • z • (psfunctor_comp _ _ _)^-1)
                        (psfunctor_lwhisker L (biadj_unit R p) (##R α)))
                  as q.
                cbn in q.
                rewrite !vassocl in q.
                rewrite vcomp_rinv in q.
                rewrite id2_right in q.
                rewrite !vassocr in q.
                rewrite vcomp_linv in q.
                rewrite id2_left in q.
                exact q.
              }
              exact (!(rwhisker_vcomp _ _ _)).
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply rwhisker_lwhisker_rassociator.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              refine (lwhisker_vcomp _ _ _ @ _).
              etrans.
              {
                apply maponpaths.
                pose (maponpaths
                        (λ z, (psnaturality_of (biadj_counit R) _)^-1
                              • z
                              • (psnaturality_of (biadj_counit R) _)^-1)
                        (psnaturality_natural (biadj_counit R) _ _ _ _ α))
                  as q.
                cbn in q.
                rewrite !vassocl in q.
                rewrite vcomp_rinv in q.
                rewrite id2_right in q.
                rewrite !vassocr in q.
                rewrite vcomp_linv in q.
                rewrite id2_left in q.
                exact (!q).
              }
              exact (!(lwhisker_vcomp _ _ _)).
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (lwhisker_vcomp _ _ _ @ _).
            etrans.
            {
              apply maponpaths.
              apply lwhisker_lwhisker.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        etrans.
        {
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            rewrite lwhisker_vcomp.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply vcomp_whisker.
            }
            exact (!(lwhisker_vcomp _ _ _)).
          }
          apply vassocl.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(lwhisker_vcomp _ _ _)).
        }
        refine (vassocl _ _ _ @ _).
        apply maponpaths.
        refine (lwhisker_vcomp _ _ _ @ _ @ !(lwhisker_vcomp _ _ _)).
        apply maponpaths.
        refine (!_).
        apply vcomp_lunitor.
    Qed.

    Transparent psfunctor_comp.

    Definition left_biadj_preserves_bincoprod_nat_trans
      : left_biadj_preserves_binprods_1cell x p
        ⟹
        universal_coprod_functor (psfunctor_bincoprod_cocone L p) x.
    Proof.
      use make_nat_trans.
      - exact left_biadj_preserves_bincoprod_nat_trans_data.
      - exact left_biadj_preserves_bincoprod_is_nat_trans.
    Defined.

    Definition left_biadj_preserves_bincoprod_is_nat_z_iso
      : is_nat_z_iso left_biadj_preserves_bincoprod_nat_trans.
    Proof.
      intro.
      use is_z_iso_binprod_z_iso.
      + use is_inv2cell_to_is_z_iso.
        is_iso ; apply property_from_invertible_2cell.
      + use is_inv2cell_to_is_z_iso.
        is_iso ; apply property_from_invertible_2cell.
    Defined.

    Definition left_biadj_preserves_bincoprod_nat_z_iso
      : nat_z_iso
          (left_biadj_preserves_binprods_1cell x p)
          (universal_coprod_functor (psfunctor_bincoprod_cocone L p) x).
    Proof.
      use make_nat_z_iso.
      - exact left_biadj_preserves_bincoprod_nat_trans.
      - exact left_biadj_preserves_bincoprod_is_nat_z_iso.
    Defined.
  End PreserveCoproducts.

  Definition left_biadj_preserves_binprods
             (HB₁ : is_univalent_2_1 B₁)
             (HB₂ : is_univalent_2_1 B₂)
    : preserves_bincoprods L.
  Proof.
    intros y₁ y₂ p Hp.
    use universal_coprod_cocone_has_ump.
    intro x.
    use nat_iso_adj_equivalence_of_cats.
    - exact (left_biadj_preserves_binprods_1cell x p).
    - exact (left_biadj_preserves_bincoprod_nat_trans p x).
    - exact (left_biadj_preserves_bincoprod_is_nat_z_iso p x).
    - exact (left_biadj_preserves_binprods_1cell_adj_equiv HB₁ x p Hp).
  Defined.
End BiadjunctionPreservation.
