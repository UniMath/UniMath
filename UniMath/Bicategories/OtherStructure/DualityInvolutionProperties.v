(***********************************************************************************

 Properties of duality involutions

 In this file, we define several operations for duality involutions and we prove
 several properties for them. More specifically, we construct the transpose of
 morphisms, and we show that this gives rise to an adjoint equivalence on the
 hom-categories ([adj_equivalence_duality_transpose]). Note that we assume here
 that the bicategory is locally univalent, so that we can use that every fully
 faithful and essentially surjective is an adjoint equivalence. In addition, we
 prove that every duality involution is a local equivalence.

 Duality involutions satisfy two coherences:
 - One expresse that the triangle 2-cell is a modification
 - The other expresses that the obtained biadjunction is coherent. This law is also
   known as the swallowtail equation.
 We only need the first coherence of these in the remainder of this file. The reason
 for that is as follows. When one expresses a biadjunction as a pseudonatural
 equivalence between the hom-categories, then the swallowtail equation expresses
 that this equivalence is actually an adjoint equivalence of categories. While we
 also construct an adjoint equivalence on the hom-categories, we do so by showing
 that every fully faithful and essentially surjective functor is an adjoint
 equivalence. As such, we do not need to verify the triangle equations ourselves,
 and thus we do not need this second coherence of duality involutions.

 Contents
 1. Transposes of duality involutions
 2. Duality involutions are local equivalences

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Properties.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.OtherStructure.DualityInvolution.

Local Open Scope cat.

(** * 1. Transposes of duality involutions *)
Section DualityInvolutionAccessors.
  Context {B : bicat}
          (L : psfunctor (op2_bicat B) B)
          (HL : duality_involution L).

  Let R : psfunctor B (op2_bicat B) := op2_psfunctor L.

  Let η : pstrans (id_psfunctor _) (comp_psfunctor L R) := unit_of_duality HL.
  Let ηinv : pstrans (comp_psfunctor L R) (id_psfunctor _) := unit_inv_of_duality HL.

  Definition duality_transpose
             {x y : B}
             (f : x --> L y)
    : L x --> y
    := #L f · ηinv y.

  Definition duality_transpose_cell
             {x y : B}
             {f₁ f₂ : x --> L y}
             (τ : f₂ ==> f₁)
    : duality_transpose f₁ ==> duality_transpose f₂
    := ##L τ ▹ ηinv y.

  Definition duality_transpose_functor_data
             (x y : B)
    : functor_data
        (@hom (op2_bicat B) x (L y))
        (hom (L x) y).
  Proof.
    use make_functor_data.
    - exact duality_transpose.
    - exact (λ _ _ τ, duality_transpose_cell τ).
  Defined.

  Definition duality_transpose_is_functor
             (x y : B)
    : is_functor (duality_transpose_functor_data x y).
  Proof.
    split.
    - intro f ; cbn ; unfold duality_transpose_cell.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      apply (psfunctor_id2 L).
    - intros f₁ f₂ f₃ τ₁ τ₂ ; cbn ; unfold duality_transpose_cell.
      refine (_ @ !(rwhisker_vcomp _ _ _)).
      apply maponpaths.
      apply (psfunctor_vcomp L).
  Qed.

  Definition duality_transpose_functor
             (x y : B)
    : @hom (op2_bicat B) x (L y) ⟶ hom (L x) y.
  Proof.
    use make_functor.
    - exact (duality_transpose_functor_data x y).
    - exact (duality_transpose_is_functor x y).
  Defined.

  Section EssentiallySurjective.
    Context {x y : B}
            (f : L x --> y).

    Definition duality_involution_preimage
      : x --> L y
      := η x · #L f.

    Definition duality_involution_preimage_inv2cell
      : invertible_2cell
          (duality_transpose_functor x y duality_involution_preimage)
          f.
    Proof.
      unfold duality_involution_preimage ; cbn ; unfold duality_transpose.
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (inv_of_invertible_2cell (psfunctor_comp L (η x) (#L f))))
                _).
      refine (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                _).
      refine (comp_of_invertible_2cell
                (lwhisker_of_invertible_2cell
                   _
                   (inv_of_invertible_2cell (psnaturality_of ηinv f)))
                _).
      refine (comp_of_invertible_2cell
                (lassociator_invertible_2cell _ _ _)
                _).
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell _ _)
                (lunitor_invertible_2cell _)).
      cbn.
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (inv_of_invertible_2cell (triangle_data_of_duality HL x)))
                _).
      exact (inv_of_invertible_2cell
               (invertible_modcomponent_of (unit_unit_inv_of_duality HL) (L x))).
    Defined.
  End EssentiallySurjective.

  Proposition essentially_surjective_duality_transpose
              (x y : B)
    : essentially_surjective (duality_transpose_functor x y).
  Proof.
    intros f.
    refine (hinhpr (duality_involution_preimage f ,, _)).
    use inv2cell_to_z_iso.
    exact (duality_involution_preimage_inv2cell f).
  Defined.


  Definition duality_involution_local_equivalence_inv2cell
             {x y : B}
             (f : x --> y)
    : invertible_2cell (η x · # L(#L f) · ηinv y) f.
  Proof.
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (psnaturality_of η f))
              _).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              _
              (runitor_invertible_2cell _)).
    refine (lwhisker_of_invertible_2cell _ _).
    exact (inv_of_invertible_2cell
             (invertible_modcomponent_of (unit_unit_inv_of_duality HL) y)).
  Defined.

  Definition duality_involution_inv_of_2cell
             {x y : B}
             {f g : x --> y}
             (τ : # L f ==> # L g)
    : g ==> f.
  Proof.
    refine (_ • (η x ◃ ##L τ ▹ ηinv y) • _).
    - exact ((duality_involution_local_equivalence_inv2cell g)^-1).
    - exact (duality_involution_local_equivalence_inv2cell f).
  Defined.

  Proposition duality_involution_inv_of_2cell_eq
              {x y : B}
              {f g : x --> y}
              (τ : # L f ==> # L g)
    : ##L (duality_involution_inv_of_2cell τ) = τ.
  Proof.
    unfold duality_involution_inv_of_2cell.
    rewrite !vassocl.
    refine (psfunctor_vcomp L _ _ @ _).
    use (vcomp_rcancel (## L(duality_involution_local_equivalence_inv2cell g))).
    {
      use (psfunctor_is_iso L (make_invertible_2cell _)).
      use to_op2_is_invertible_2cell.
      apply duality_involution_local_equivalence_inv2cell.
    }
    rewrite !vassocl.
    rewrite <- psfunctor_vcomp.
    etrans.
    {
      do 2 apply maponpaths.
      apply (vcomp_rinv (duality_involution_local_equivalence_inv2cell g)).
    }
    etrans.
    {
      apply maponpaths.
      apply (psfunctor_id2 L).
    }
    rewrite id2_right.
    unfold duality_involution_local_equivalence_inv2cell.
    simpl.
    refine (psfunctor_vcomp L _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (psfunctor_vcomp L _ _ @ _).
      apply maponpaths_2.
      refine (psfunctor_vcomp L _ _ @ _).
      apply maponpaths_2.
      apply (psfunctor_vcomp L).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (psfunctor_vcomp L _ _ @ _).
      apply maponpaths_2.
      refine (psfunctor_vcomp L _ _ @ _).
      apply maponpaths_2.
      apply (psfunctor_vcomp L).
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (psfunctor_rinvunitor L g).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (psfunctor_rinvunitor L f).
    }
    rewrite !vassocr.
    refine (!_).
    etrans.
    {
      do 5 apply maponpaths_2.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      apply (psfunctor_lwhisker L).
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      apply (psfunctor_lwhisker L).
    }
    rewrite !vassocl.
    apply maponpaths.
    use (vcomp_lcancel (#L f ◃ psfunctor_comp L (η y) (ηinv y))).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      exact (psfunctor_lassociator L f (η y) (ηinv y)).
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      apply (psfunctor_rwhisker L).
    }
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      apply (psfunctor_rwhisker L).
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      exact (psfunctor_lassociator L g (η y) (ηinv y)).
    }
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      apply (psfunctor_rwhisker L).
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !rwhisker_vcomp.
    apply maponpaths.
    rewrite !vassocl.
    use (vcomp_lcancel (_ ◃ triangle_data_of_duality HL y)).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite !vassocl.
    use (vcomp_lcancel (psnaturality_of η (# L f))).
    {
      apply property_from_invertible_2cell.
    }
    rewrite !vassocr.
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (!(psnaturality_natural η _ _ _ _ τ)).
    }
    cbn -[psfunctor_comp].
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      refine (!_).
      apply (duality_to_triangle_law HL).
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      refine (!_).
      apply maponpaths_2.
      apply (duality_to_triangle_law HL).
    }
    rewrite !vassocl.
    apply maponpaths.
    apply (psfunctor_lwhisker L).
  Qed.

  Section Fullness.
    Context {x y : B}
            {f g : x --> L y}
            (τ : duality_transpose f ==> duality_transpose g).

    Let Hf : fully_faithful_1cell (ηinv y)
      := adj_equiv_fully_faithful (left_adjoint_equivalance_duality_unit_inv_pointwise HL y).

    Definition full_duality_transpose_inv
      : g ==> f
      := duality_involution_inv_of_2cell (fully_faithful_1cell_inv_map Hf τ).

    Proposition full_duality_transpose_inv_eq
      : duality_transpose_cell full_duality_transpose_inv = τ.
    Proof.
      unfold duality_transpose_cell.
      unfold duality_transpose in τ.
      refine (_ @ fully_faithful_1cell_inv_map_eq Hf τ).
      apply maponpaths.
      apply duality_involution_inv_of_2cell_eq.
    Qed.
  End Fullness.

  Proposition full_duality_transpose
              (x y : B)
    : full (duality_transpose_functor x y).
  Proof.
    intros f g τ ; cbn in f, g, τ.
    unfold duality_transpose in τ.
    simple refine (hinhpr (_ ,, _)).
    - exact (full_duality_transpose_inv τ).
    - exact (full_duality_transpose_inv_eq τ).
  Qed.

  Proposition faithful_duality_transpose
              (x y : B)
    : faithful (duality_transpose_functor x y).
  Proof.
    intros f g τ ; cbn in f, g, τ.
    use invproofirrelevance.
    intros φ₁ φ₂.
    induction φ₁ as [ φ₁ p₁ ].
    induction φ₂ as [ φ₂ p₂ ].
    cbn in φ₁, φ₂, p₁, p₂.
    unfold duality_transpose_cell in p₁, p₂.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    cbn.
    use lwhisker_id_inj.
    use (vcomp_rcancel (invertible_modcomponent_of (unit_unit_inv_of_duality HL) x ▹ _)).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    rewrite <- !vcomp_whisker.
    apply maponpaths.
    use (vcomp_rcancel (rassociator _ _ _)).
    {
      is_iso.
    }
    etrans.
    {
      refine (!_).
      apply lwhisker_lwhisker_rassociator.
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply lwhisker_lwhisker_rassociator.
    }
    refine (!_).
    do 2 apply maponpaths.
    use (vcomp_rcancel (psnaturality_of ηinv f)).
    {
      apply property_from_invertible_2cell.
    }
    refine (psnaturality_natural ηinv _ _ _ _ φ₁ @ _).
    refine (_ @ !(psnaturality_natural ηinv _ _ _ _ φ₂)).
    apply maponpaths.
    cbn.
    use (vcomp_rcancel ((#L(#L f)) ◃ triangle_data_of_duality_inv HL y)).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    rewrite !vcomp_whisker.
    apply maponpaths.
    use (vcomp_rcancel (psfunctor_comp L _ _)).
    {
      apply property_from_invertible_2cell.
    }
    refine (!(psfunctor_rwhisker L _ _) @ _ @ psfunctor_rwhisker L _ _).
    apply maponpaths.
    exact (maponpaths (λ z, ##R z) (p₁ @ !p₂)).
  Qed.

  Proposition fully_faithful_duality_transpose
              (x y : B)
    : fully_faithful (duality_transpose_functor x y).
  Proof.
    use full_and_faithful_implies_fully_faithful.
    split.
    - exact (full_duality_transpose x y).
    - exact (faithful_duality_transpose x y).
  Qed.

  Definition adj_equivalence_duality_transpose
             (HB : is_univalent_2_1 B)
             (x y : B)
    : adj_equivalence_of_cats (duality_transpose_functor x y).
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      use op2_bicat_is_univalent_2_1.
      exact HB.
    - exact (fully_faithful_duality_transpose x y).
    - exact (essentially_surjective_duality_transpose x y).
  Defined.

  (** * 2. Duality involutions are local equivalences *)
  Section LocalEquivalence.
    Context (HB : is_univalent_2_1 B).

    Let HB' : is_univalent_2_1 (op2_bicat B) := op2_bicat_is_univalent_2_1 HB.

    Definition duality_involution_inv_mor
               {x y : B}
               (f : L x --> L y)
      : x --> y
      := η x · #L f · ηinv y.

    Definition duality_involution_inv_mor_inv2cell
               {x y : B}
               (f : L x --> L y)
      : invertible_2cell (#L (duality_involution_inv_mor f)) f.
    Proof.
      unfold duality_involution_inv_mor.
      refine (comp_of_invertible_2cell
                (inv_of_invertible_2cell (psfunctor_comp L _ _))
                _).
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (inv_of_invertible_2cell (psfunctor_comp L _ _)))
                _).
      refine (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                _).
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (inv_of_invertible_2cell
                      (triangle_data_of_duality HL x)))
                _).
      refine (comp_of_invertible_2cell
                (lassociator_invertible_2cell _ _ _)
                _).
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (psnaturality_of η f))
                _).
      refine (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                _).
      refine (comp_of_invertible_2cell
                _
                (runitor_invertible_2cell _)).
      refine (lwhisker_of_invertible_2cell _ _).
      refine (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell
                   _
                   (triangle_data_of_duality HL y))
                _).
      refine (comp_of_invertible_2cell
                (psfunctor_comp L _ _)
                _).
      refine (comp_of_invertible_2cell
                _
                (inv_of_invertible_2cell (psfunctor_id L _))).
      use (psfunctor_inv2cell L).
      exact (make_invertible_2cell
               (to_op2_is_invertible_2cell
                  (invertible_modcomponent_of
                     (unit_unit_inv_of_duality HL)
                     y))).
    Defined.

    Proposition duality_involution_inv_of_2cell_psfunctor_eq
                {x y : B}
                {f g : x --> y}
                (τ : g ==> f)
      : duality_involution_inv_of_2cell (## L τ) = τ.
    Proof.
      unfold duality_involution_inv_of_2cell.
      simpl.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ].
      simpl.
      rewrite <- vcomp_runitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact (psnaturality_natural η _ _ _ _ τ).
        }
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      refine (_ @ id2_right _).
      apply maponpaths.
      rewrite <- lwhisker_id2.
      apply maponpaths.
      exact (vcomp_rinv (invertible_modcomponent_of (unit_unit_inv_of_duality HL) y)).
    Qed.

    Definition duality_involution_local_equivalence
      : local_equivalence HB' HB L.
    Proof.
      use make_local_equivalence.
      - exact (λ x y f, duality_involution_inv_mor f).
      - exact (λ x y f, duality_involution_inv_mor_inv2cell f).
      - exact (λ x y f g τ, duality_involution_inv_of_2cell τ).
      - intros x y f g τ.
        apply duality_involution_inv_of_2cell_eq.
      - intros x y f g τ.
        apply duality_involution_inv_of_2cell_psfunctor_eq.
    Defined.
  End LocalEquivalence.
End DualityInvolutionAccessors.
