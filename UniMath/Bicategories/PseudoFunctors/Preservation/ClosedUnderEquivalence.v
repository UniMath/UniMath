Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.ProductEquivalences.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.InserterEquivalences.
Require Import UniMath.Bicategories.Limits.Equifiers.
Require Import UniMath.Bicategories.Limits.EquifierEquivalences.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.
Require Import UniMath.Bicategories.Colimits.CoproductEquivalences.

Local Open Scope cat.

Section PreservationClosedUnderEquivalence.
  Context {B₁ B₂ : bicat}
          {F G : psfunctor B₁ B₂}
          (η : pstrans F G)
          (Hη : ∏ (x : B₁), left_adjoint_equivalence (η x)).

  Definition preserves_bifinal_left_adjoint_equivalence
             (HF : preserves_bifinal F)
    : preserves_bifinal G.
  Proof.
    intros x Hx.
    exact (is_bifinal_left_adjoint_equivalence
             _
             (Hη x)
             (HF _ Hx)).
  Defined.

  Definition preserves_biinitial_left_adjoint_equivalence
             (HF : preserves_biinitial F)
    : preserves_biinitial G.
  Proof.
    intros x Hx.
    exact (equiv_from_biinitial
             (HF _ Hx)
             (Hη x)).
  Defined.

  Definition preserves_binprods_left_adjoint_equivalence
             (HF : preserves_binprods F)
    : preserves_binprods G.
  Proof.
    intros x y p Hp.
    exact (has_binprod_ump_left_adjoint_equivalence
             _ _
             (HF _ _ _ Hp)
             _ _
             _ _ _
             (Hη x)
             (Hη y)
             (Hη p)
             (psnaturality_of
                η
                (binprod_cone_pr1 p))
             (psnaturality_of
                η
                (binprod_cone_pr2 p))).
  Defined.

  Definition preserves_bincoprods_left_adjoint_equivalence
             (HF : preserves_bincoprods F)
    : preserves_bincoprods G.
  Proof.
    intros x y p Hp.
    exact (has_bincoprod_ump_left_adjoint_equivalence
             _ _
             (HF _ _ _ Hp)
             _ _
             _ _ _
             (Hη x)
             (Hη y)
             (Hη p)
             (psnaturality_of
                η
                (bincoprod_cocone_inl p))
             (psnaturality_of
                η
                (bincoprod_cocone_inr p))).
  Defined.

  Definition preserves_inserters_left_adjoint_equivalence
             (HF : preserves_inserters F)
    : preserves_inserters G.
  Proof.
    intros x y f g p Hp.
    use (has_inserter_ump_left_adjoint_equivalence
             _ _ _
             (Hη x)
             (Hη y)
             (Hη p)
             (psnaturality_of η (inserter_cone_pr1 p))
             (psnaturality_of η f)
             (psnaturality_of η g)
             (HF _ _ _ _ _ Hp)).
    abstract
      (pose (psnaturality_natural η _ _ _ _ (inserter_cone_cell p)) as q ;
       cbn in q ;
       rewrite (pstrans_comp_alt η (inserter_cone_pr1 p) g) in q ;
       rewrite (pstrans_comp_alt η (inserter_cone_pr1 p) f) in q ;
       rewrite !vassocl in q ;
       rewrite <- !lwhisker_vcomp ;
       rewrite <- !rwhisker_vcomp ;
       rewrite !vassocr ;
       use vcomp_move_L_Mp ; [ is_iso | ] ;
       cbn -[psfunctor_comp] ;
       rewrite !vassocl ;
       rewrite q ;
       rewrite !vassocr ;
       do 6 apply maponpaths_2 ;
       rewrite !lwhisker_vcomp ;
       rewrite vcomp_rinv ;
       rewrite lwhisker_id2 ;
       apply id2_left).
  Defined.

  Definition preserves_equifiers_left_adjoint_equivalence
             (HF : preserves_equifiers F)
    : preserves_equifiers G.
  Proof.
    intros x y f g α β p Hp.
    exact (has_equifier_ump_left_adjoint_equivalence
             _ _ _ _ _
             (Hη x)
             (Hη y)
             (Hη p)
             (psnaturality_of η (equifier_cone_pr1 p))
             (psnaturality_of η f)
             (psnaturality_of η g)
             (HF _ _ _ _ _ _ _ Hp)
             (psnaturality_natural η _ _ _ _ α)
             (psnaturality_natural η _ _ _ _ β)).
  Defined.
End PreservationClosedUnderEquivalence.
