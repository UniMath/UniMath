(**
Restrict pseudofunctor to its full image.
We also give conditions when it gives rise to a weak equivalence.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.Image.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Section CorestrictImage.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂).

  Definition corestrict_full_image_data
    : psfunctor_data B₁ (full_image F).
  Proof.
    use make_psfunctor_data.
    - exact (λ x, F x ,, hinhpr (x ,, idpath (F x))).
    - exact (λ _ _ f, #F f ,, tt).
    - exact (λ _ _ _ _ α, ##F α ,, tt).
    - exact (λ x, pr1 (psfunctor_id F x) ,, tt).
    - exact (λ _ _ _ f g, pr1 (psfunctor_comp F f g) ,, tt).
  Defined.

  Definition corestrict_full_image_laws
    : psfunctor_laws corestrict_full_image_data.
  Proof.
    repeat split
    ; intro ; intros ; (use subtypePath ; [ intro ; apply isapropunit | apply F ]).
  Qed.

  Definition corestrict_full_image_invertibles
    : invertible_cells corestrict_full_image_data.
  Proof.
    split ; intro ; intros
    ; apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell
    ; apply F.
  Defined.

  Definition corestrict_full_image
    : psfunctor B₁ (full_image F).
  Proof.
    use make_psfunctor.
    - exact corestrict_full_image_data.
    - exact corestrict_full_image_laws.
    - exact corestrict_full_image_invertibles.
  Defined.

  Definition corestrict_full_image_essentially_surjective
    : essentially_surjective corestrict_full_image.
  Proof.
    intros x.
    induction x as [x₁ x₂].
    simpl in x₂.
    revert x₂.
    use squash_rec.
    intro x.
    simpl.
    apply hinhpr.
    refine (pr1 x ,, _).
    apply bicat_adjoint_equivalence_is_fullsub_adjoint_equivalence.
    exact (idtoiso_2_0 _ _ (pr2 x)).
  Defined.

  Section CorestrictFullImageLocalEquivalence.
    Variable (B₁_is_univalent_2_1 : is_univalent_2_1 B₁)
             (B₂_is_univalent_2_1 : is_univalent_2_1 B₂)
             (FI_is_univalent_2_1 : is_univalent_2_1 (full_image F))
             (F_local_equiv : local_equivalence
                                B₁_is_univalent_2_1
                                B₂_is_univalent_2_1
                                F).

    Definition corestrict_full_image_local_equivalence_right_adj
               (x y : B₁)
      : bicat_of_univ_cats
          ⟦ univ_hom
              FI_is_univalent_2_1
              (corestrict_full_image x)
              (corestrict_full_image y),
            univ_hom B₁_is_univalent_2_1 x y ⟧.
    Proof.
      pose (G := F_local_equiv x y).
      use make_functor.
      - use make_functor_data.
        + exact (λ z, pr1 (left_adjoint_right_adjoint G) (pr1 z)).
        + exact (λ _ _ f, # (pr1 (left_adjoint_right_adjoint G)) (pr1 f)).
      - split.
        + abstract
            (intro a ;
             exact (functor_id (left_adjoint_right_adjoint G) (pr1 a))).
        + abstract
            (intros ? ? ? f g ;
             exact (functor_comp (left_adjoint_right_adjoint G) (pr1 f) (pr1 g))).
    Defined.

    Definition corestrict_full_image_local_equivalence
      : local_equivalence
          B₁_is_univalent_2_1
          FI_is_univalent_2_1
          corestrict_full_image.
    Proof.
      intros x y.
      use equiv_to_isadjequiv.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact (corestrict_full_image_local_equivalence_right_adj x y).
      - use make_nat_trans.
        + exact (λ z, pr1 (left_adjoint_unit (F_local_equiv x y)) z).
        + abstract
            (intros a b g ;
             exact (pr2 (left_adjoint_unit (F_local_equiv x y)) _ _ g)).
      - use make_nat_trans.
        + exact (λ z, pr1 (left_adjoint_counit (F_local_equiv x y)) (pr1 z) ,, tt).
        + abstract
            (intros a b g ;
             use subtypePath ; [ intro ; apply isapropunit | ] ;
             exact (pr2 (left_adjoint_counit (F_local_equiv x y)) _ _ (pr1 g))).
      - apply is_nat_iso_to_is_invertible_2cell.
        intro z.
        exact (is_invertible_2cell_to_is_nat_iso
                 _
                 (left_equivalence_unit_iso (F_local_equiv x y)) z).
      - apply is_nat_iso_to_is_invertible_2cell.
        intro z.
        apply is_inv2cell_to_is_iso.
        apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
        apply (iso_to_inv2cell
                (_ ,,
                   is_invertible_2cell_to_is_nat_iso
                   _
                   (left_equivalence_counit_iso (F_local_equiv x y)) (pr1 z))).
    Defined.
  End CorestrictFullImageLocalEquivalence.

  Definition corestrict_full_image_weak_equivalence
             (B₁_is_univalent_2_1 : is_univalent_2_1 B₁)
             (B₂_is_univalent_2_1 : is_univalent_2_1 B₂)
             (FI_is_univalent_2_1 : is_univalent_2_1 (full_image F))
             (F_local_equiv : local_equivalence
                                B₁_is_univalent_2_1
                                B₂_is_univalent_2_1
                                F)
    : weak_equivalence
        B₁_is_univalent_2_1
        FI_is_univalent_2_1
        corestrict_full_image.
  Proof.
    split.
    - exact (corestrict_full_image_local_equivalence _ _ _ F_local_equiv).
    - apply corestrict_full_image_essentially_surjective.
  Defined.
End CorestrictImage.
