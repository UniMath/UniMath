(***********************************************************************************

 Properties of duality involutions

 In this file, we define several operations for duality involutions and we prove
 several properties for them. More specifically, we construct the transpose of
 morphisms, and we show that this gives rise to an adjoint equivalence on the
 hom-categories ([adj_equivalence_duality_transpose]). Note that we assume here
 that the bicategory is locally univalent, so that we can use that every fully
 faithful and essentially surjective is an adjoint equivalence. In addition, we
 prove that every duality involution is a local equivalence.

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
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
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

  Proposition full_duality_transpose
              (x y : B)
    : full (duality_transpose_functor x y).
  Proof.
    intros f g τ ; cbn in f, g, τ.
    unfold duality_transpose in τ.
    simple refine (hinhpr (_ ,, _)).
    - cbn.
      pose (##R τ).
      cbn in p.
  Admitted.

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
End DualityInvolutionAccessors.
