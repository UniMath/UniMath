(*****************************************************************

 Structure on the bicategory of enriched category

 In this file, we construct a duality involution of the bicategory
 of enriched categories.

 Contents
 1. Duality involution on enriched categories

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctorEnriched.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.OtherStructure.DualityInvolution.

Local Open Scope cat.

(**
 1. Duality involution on enriched categories
 *)
Section DualityInvolutionEnriched.
  Context (V : sym_monoidal_cat).

  Definition bicat_of_enriched_cat_duality_unit_data
    : pstrans_data
        (id_psfunctor (bicat_of_enriched_cats V))
        (comp_psfunctor
           (op_enriched_psfunctor V)
           (op2_psfunctor (op_enriched_psfunctor V))).
  Proof.
    use make_pstrans_data.
    - cbn.
      exact (λ E, functor_identity _ ,, op_enriched_unit V (pr2 E)).
    - intros E₁ E₂ F.
      use make_invertible_2cell.
      + exact (op_unit_nat_trans (pr1 F)
               ,,
               op_enriched_unit_naturality V (pr2 F)).
      + use make_is_invertible_2cell.
        * exact (nat_z_iso_to_trans_inv (op_unit_nat_z_iso (pr1 F))
                 ,,
                 op_enriched_unit_naturality_inv V (pr2 F)).
        * abstract
            (use eq_2cell_enriched ;
             intro x ; cbn ;
             apply id_left).
        * abstract
            (use eq_2cell_enriched ;
             intro x ; cbn ;
             apply id_left).
  Defined.

  Proposition bicat_of_enriched_cat_duality_unit_is_pstrans
    : is_pstrans bicat_of_enriched_cat_duality_unit_data.
  Proof.
    repeat split.
    - intros E₁ E₂ F G α.
      use eq_2cell_enriched.
      intro x ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros E.
      use eq_2cell_enriched.
      intros x ; cbn.
      apply idpath.
    - intros E₁ E₂ E₃ F G.
      use eq_2cell_enriched.
      intros x ; cbn.
      rewrite functor_id.
      rewrite !id_left.
      apply idpath.
  Qed.

  Definition bicat_of_enriched_cat_duality_unit
    : pstrans
        (id_psfunctor (bicat_of_enriched_cats V))
        (comp_psfunctor
           (op_enriched_psfunctor V)
           (op2_psfunctor (op_enriched_psfunctor V))).
  Proof.
    use make_pstrans.
    - exact bicat_of_enriched_cat_duality_unit_data.
    - exact bicat_of_enriched_cat_duality_unit_is_pstrans.
  Defined.

  Definition bicat_of_enriched_cat_duality_unit_inv_data
    : pstrans_data
        (comp_psfunctor
           (op_enriched_psfunctor V)
           (op2_psfunctor (op_enriched_psfunctor V)))
        (id_psfunctor (bicat_of_enriched_cats V)).
  Proof.
    use make_pstrans_data.
    - cbn.
      exact (λ E, functor_identity _ ,, op_enriched_unit_inv V (pr2 E)).
    - intros E₁ E₂ F.
      use make_invertible_2cell.
      + exact (op_unit_inv_nat_trans (pr1 F)
               ,,
               op_enriched_unit_inv_naturality V (pr2 F)).
      + use make_is_invertible_2cell.
        * exact (nat_z_iso_to_trans_inv (op_unit_inv_nat_z_iso (pr1 F))
                 ,,
                 op_enriched_unit_inv_naturality_inv V (pr2 F)).
        * abstract
            (use eq_2cell_enriched ;
             intro x ; cbn ;
             apply id_left).
        * abstract
            (use eq_2cell_enriched ;
             intro x ; cbn ;
             apply id_left).
  Defined.

  Proposition bicat_of_enriched_cat_duality_unit_inv_is_pstrans
    : is_pstrans bicat_of_enriched_cat_duality_unit_inv_data.
  Proof.
    repeat split.
    - intros E₁ E₂ F G α ; simpl.
      use eq_2cell_enriched.
      intro x ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros E ; simpl.
      use eq_2cell_enriched.
      intros x ; cbn.
      rewrite !id_left.
      apply idpath.
    - intros E₁ E₂ E₃ F G ; simpl.
      use eq_2cell_enriched.
      intros x ; cbn.
      rewrite !id_left, !id_right.
      exact (!(functor_id _ _)).
  Admitted.

  Definition bicat_of_enriched_cat_duality_unit_inv
    : pstrans
        (comp_psfunctor
           (op_enriched_psfunctor V)
           (op2_psfunctor (op_enriched_psfunctor V)))
        (id_psfunctor (bicat_of_enriched_cats V)).
  Proof.
    use make_pstrans.
    - exact bicat_of_enriched_cat_duality_unit_inv_data.
    - exact bicat_of_enriched_cat_duality_unit_inv_is_pstrans.
  Defined.

  Definition bicat_of_enriched_cat_duality_unit_unit_inv_data
    : invertible_modification_data
        (id₁ (id_psfunctor (bicat_of_enriched_cats V)))
        (bicat_of_enriched_cat_duality_unit · bicat_of_enriched_cat_duality_unit_inv).
  Proof.
    intros E.
    use make_invertible_2cell.
    - exact (op_unit_unit_inv_nat_trans _ ,, op_enriched_unit_unit_inv V (pr2 E)).
    - use make_is_invertible_2cell.
      + exact (nat_z_iso_to_trans_inv (op_unit_unit_inv_nat_z_iso _)
               ,,
               op_enriched_unit_unit_inv_inv V (pr2 E)).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
  Defined.

  Proposition bicat_of_enriched_cat_duality_unit_unit_inv_laws
    : is_modification bicat_of_enriched_cat_duality_unit_unit_inv_data.
  Proof.
    intros E₁ E₂ F.
    use eq_2cell_enriched.
    intros x ; cbn.
    rewrite (functor_id (pr1 F)), !id_left.
    apply idpath.
  Qed.

  Definition bicat_of_enriched_cat_duality_unit_unit_inv
    : invertible_modification
        (id₁ (id_psfunctor (bicat_of_enriched_cats V)))
        (bicat_of_enriched_cat_duality_unit · bicat_of_enriched_cat_duality_unit_inv).
  Proof.
    use make_invertible_modification.
    - exact bicat_of_enriched_cat_duality_unit_unit_inv_data.
    - exact bicat_of_enriched_cat_duality_unit_unit_inv_laws.
  Defined.

  Definition bicat_of_enriched_cat_duality_unit_inv_unit_data
    : invertible_modification_data
        (bicat_of_enriched_cat_duality_unit_inv · bicat_of_enriched_cat_duality_unit)
        (id₁ _).
  Proof.
    intros E.
    use make_invertible_2cell.
    - exact (op_unit_inv_unit_nat_trans _
             ,,
             op_enriched_unit_inv_unit V (pr2 E)).
    - use make_is_invertible_2cell.
      + exact (nat_z_iso_to_trans_inv (op_unit_inv_unit_nat_z_iso _)
               ,,
               op_enriched_unit_inv_unit_inv V (pr2 E)).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
  Defined.

  Proposition bicat_of_enriched_cat_duality_unit_inv_unit_laws
    : is_modification bicat_of_enriched_cat_duality_unit_inv_unit_data.
  Proof.
    intros E₁ E₂ F.
    use eq_2cell_enriched.
    intro x ; cbn.
    rewrite (functor_id (pr1 F)), !id_left.
    apply idpath.
  Qed.

  Definition bicat_of_enriched_cat_duality_unit_inv_unit
    : invertible_modification
        (bicat_of_enriched_cat_duality_unit_inv · bicat_of_enriched_cat_duality_unit)
        (id₁ _).
  Proof.
    use make_invertible_modification.
    - exact bicat_of_enriched_cat_duality_unit_inv_unit_data.
    - exact bicat_of_enriched_cat_duality_unit_inv_unit_laws.
  Defined.

  Definition bicat_of_enriched_cat_duality_triangle
             (E : op2_bicat (bicat_of_enriched_cats V))
    : invertible_2cell
        (bicat_of_enriched_cat_duality_unit (op_enriched_psfunctor V E))
        (# (op_enriched_psfunctor V) (bicat_of_enriched_cat_duality_unit E)).
  Proof.
    use make_invertible_2cell.
    - exact (op_triangle_nat_trans _ ,, op_enriched_triangle V (pr2 E)).
    - use make_is_invertible_2cell.
      + exact (nat_z_iso_to_trans_inv (op_triangle_nat_z_iso _)
               ,,
               op_enriched_triangle_inv V (pr2 E)).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
      + abstract
          (use eq_2cell_enriched ;
           intros x ; cbn ;
           apply id_left).
  Defined.

  Definition bicat_of_enriched_cat_duality_data
    : duality_involution_data (op_enriched_psfunctor V).
  Proof.
    use make_duality_involution_data.
    - exact bicat_of_enriched_cat_duality_unit.
    - exact bicat_of_enriched_cat_duality_unit_inv.
    - exact bicat_of_enriched_cat_duality_unit_unit_inv.
    - exact bicat_of_enriched_cat_duality_unit_inv_unit.
    - exact bicat_of_enriched_cat_duality_triangle.
  Defined.

  Definition bicat_of_enriched_cat_duality_laws
    : duality_involution_laws bicat_of_enriched_cat_duality_data.
  Proof.
    split.
    - intro E.
      use eq_2cell_enriched.
      intro x ; cbn.
      apply id_left.
    - intros E₁ E₂ F.
      use eq_2cell_enriched.
      intro x ; cbn.
      rewrite !id_left.
      exact (!(functor_id _ _)).
  Qed.

  Definition bicat_of_enriched_cat_duality
    : duality_involution (op_enriched_psfunctor V)
    := bicat_of_enriched_cat_duality_data ,, bicat_of_enriched_cat_duality_laws.
End DualityInvolutionEnriched.
