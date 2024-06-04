(******************************************************************************************

 The biequivalence for local properties

 In this file, we extend the biequivalence between univalent categories with finite limits
 and DFL full comprehension categories to take a local categorical property into account.

 Perhaps the most interesting part of the construction might be the simplicity: this is due
 to the fact that the definition of local properties has been designed in such a way that this
 biequivalence would write itself. By inspecting the proof, we can see why each requirement
 of a local property is necessary.

 To extend this biequivalence, the first thing that we need to do is to extend the
 pseudofunctor from univalent categories with finite limits to full DFL comprehension
 categories so that the categorical property is taken into account. Here we construct a
 biequivalence between two subbicategories, so the coherences become trivial and for all
 necessary 2-cells we use the unit type. However, there are some things that we must do.
 - If we have a category `C` with finite limits, then we must that the codomain has the
   fiberwise property specified by `P`. Since `P` is a local property, we must verify that
   each slice category `C/x` of `C` satisfies `P`. This is given by [local_property_slice].
 - Satisfying a categorical property fiberwise also requires one to show that the pullback
   functors preserve the property. This is the requirement [local_property_pb].
 - Finally, we must show that this action is pseudofunctorial. This means that the fiber
   functors must preserve the property as well. More concretely, if we have a functor `F` from
   `C₁` to `C₂`, then `F` gives rise to a displayed functor `FF` from the displayed codomain
   category on `C₁` to the displayed codomain category on `C₂`. The fiber functors of `FF` must
   also preserve the property, which is given by [local_property_fiber_functor].
 This ingredients give us the first pseudofunctor.

 For the second pseudofunctor, we must show that the categorical property under consideration
 is preserved under adjoint equivalence. This follows directly from univalence. In addition,
 the preservation requirement must also be preserved under equivalence, and again, this
 follows from univalence. For the unit and counit, it suffices to show that every adjoint
 equivalence is a preserving map, and again that follows from univalence.

 Contents
 1. The extended pseudofunctor from categories to comprehension categories
 2. The extended pseudofunctor from comprehension categories to categories
 3. The unit
 4. The counit
 5. The displayed biequivalence

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.CatWithProp.

Local Open Scope cat.
Local Open Scope comp_cat.

Section LocalPropertyBiequiv.
  Context (P : local_property).

  (** * 1. The extended pseudofunctor from categories to comprehension categories *)
  Definition local_property_in_cod
             (C : univ_cat_with_finlim)
             (H : P C)
    : fiberwise_cat_property P (cleaving_of_types (finlim_to_dfl_comp_cat C)).
  Proof.
    use make_fiberwise_cat_property.
    - exact (λ x, local_property_slice P C x H).
    - exact (λ x y f, local_property_pb P _ f).
  Defined.

  Proposition local_property_in_cod_functor
              {C₁ C₂ : univ_cat_with_finlim}
              {F : functor_finlim C₁ C₂}
              {H₁ : P C₁}
              {H₂ : P C₂}
              (HF : cat_property_functor P H₁ H₂ F)
    : fiberwise_cat_property_functor
        (comp_cat_type_functor
           (finlim_to_dfl_comp_cat_functor F))
        (local_property_in_cod _ H₁)
        (local_property_in_cod _ H₂).
  Proof.
    use local_property_fiber_functor.
    exact HF.
  Qed.

  Definition finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
    : disp_psfunctor
        (disp_bicat_of_univ_cat_with_cat_property P)
        (disp_bicat_of_cat_property_dfl_full_comp_cat P)
        finlim_biequiv_dfl_comp_cat_psfunctor.
  Proof.
    use make_disp_psfunctor_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - exact (λ C H, local_property_in_cod C (pr1 H) ,, tt).
    - exact (λ _ _ _ _ _ HF, tt ,, local_property_in_cod_functor (pr2 HF)).
  Defined.

  (** * 2. The extended pseudofunctor from comprehension categories to categories *)
  Definition local_property_in_dfl_comp_cat
             (C : dfl_full_comp_cat)
             (H : fiberwise_cat_property P (cleaving_of_types C))
    : P C.
  Proof.
    refine (cat_property_ob_adj_equiv_f' P _ _ _ (dfl_full_comp_cat_adjequiv_base C) (H _)).
    - apply is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    - apply univalent_category_is_univalent.
  Qed.

  Definition local_property_in_dfl_comp_cat_functor
             {C₁ C₂ : dfl_full_comp_cat}
             {F : dfl_full_comp_cat_functor C₁ C₂}
             {H₁ : fiberwise_cat_property P (cleaving_of_types C₁)}
             {H₂ : fiberwise_cat_property P (cleaving_of_types C₂)}
             (HF : fiberwise_cat_property_functor (comp_cat_type_functor F) H₁ H₂)
    : cat_property_functor
        P
        (local_property_in_dfl_comp_cat C₁ H₁)
        (local_property_in_dfl_comp_cat C₂ H₂)
        F.
  Proof.
    refine (cat_property_functor_nat_z_iso_adj_equiv_f'
              P
              _ _ _ _
              _ _
              (dfl_functor_nat_z_iso F)
              (HF _)).
    - apply is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    - apply univalent_category_is_univalent.
    - apply is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
    - apply univalent_category_is_univalent.
    - use comp_adj_equivalence_of_cats.
      + apply dfl_full_comp_cat_adjequiv_empty.
      + apply cod_fib_terminal.
    - pose (T := make_Terminal _ (comp_cat_functor_terminal F [] (pr2 []))).
      use comp_adj_equivalence_of_cats.
      + exact (dfl_full_comp_cat_adjequiv_terminal C₂ T).
      + exact (cod_fib_terminal T).
  Qed.

  Definition dfl_comp_cat_to_finlim_disp_psfunctor_local_property
    : disp_psfunctor
        (disp_bicat_of_cat_property_dfl_full_comp_cat P)
        (disp_bicat_of_univ_cat_with_cat_property P)
        dfl_comp_cat_to_finlim_psfunctor.
  Proof.
    use make_disp_psfunctor_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property.
    - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    - exact (λ C H, local_property_in_dfl_comp_cat C (pr1 H) ,, tt).
    - refine (λ _ _ _ _ _ HF, tt ,, local_property_in_dfl_comp_cat_functor _).
      exact (pr2 HF).
  Defined.

  (** * 3. The unit *)
  Definition finlim_dfl_comp_cat_unit_local_property
    : disp_pstrans
        (disp_pseudo_comp
           _ _ _ _ _
           finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
           dfl_comp_cat_to_finlim_disp_psfunctor_local_property)
        (disp_pseudo_id _)
        finlim_dfl_comp_cat_unit.
  Proof.
    use make_disp_pstrans_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property.
    - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    - intros C H.
      refine (tt ,, _).
      cbn.
      apply cat_property_id_functor'.
  Qed.

  Definition finlim_dfl_comp_cat_unit_local_property_pointwise_adjequiv
             {C : univ_cat_with_finlim}
             (HC : disp_bicat_of_univ_cat_with_cat_property P C)
    : disp_left_adjoint_equivalence
        (finlim_dfl_comp_cat_unit_pointwise_equiv C)
        (finlim_dfl_comp_cat_unit_local_property C HC).
  Proof.
    use disp_adjoint_equiv_disp_bicat_of_univ_cat_with_cat_property.
  Qed.

  Definition finlim_dfl_comp_cat_unit_inv_local_property
    : disp_pstrans
        (disp_pseudo_id _)
        (disp_pseudo_comp
           _ _ _ _ _
           finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
           dfl_comp_cat_to_finlim_disp_psfunctor_local_property)
        finlim_dfl_comp_cat_unit_inv.
  Proof.
    use make_disp_pstrans_inv_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property.
    - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    - apply finlim_dfl_comp_cat_unit_local_property.
    - intros.
      apply finlim_dfl_comp_cat_unit_local_property_pointwise_adjequiv.
  Qed.

  (** * 4. The counit *)
  Definition finlim_dfl_comp_cat_counit_local_property
    : disp_pstrans
        (disp_pseudo_id _)
        (disp_pseudo_comp
           _ _ _ _ _
           dfl_comp_cat_to_finlim_disp_psfunctor_local_property
           finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property)
        finlim_dfl_comp_cat_counit.
  Proof.
    use make_disp_pstrans_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - refine (λ C H, tt ,, _).
      intro x ; cbn.
      use (cat_property_adj_equivalence_of_cats'
             P
             _ _ _
             (fiber_functor_comprehension_adj_equiv C x)).
      + apply is_univalent_fiber.
        apply disp_univalent_category_is_univalent_disp.
      + apply is_univalent_fiber.
        apply disp_univalent_disp_codomain.
  Qed.

  Definition finlim_dfl_comp_cat_counit_local_property_pointwise_adjequiv
             {C : dfl_full_comp_cat}
             (HC : disp_bicat_of_cat_property_dfl_full_comp_cat P C)
    : disp_left_adjoint_equivalence
        (finlim_dfl_comp_cat_counit_pointwise_equiv C)
        (finlim_dfl_comp_cat_counit_local_property C HC).
  Proof.
    use disp_adjoint_equiv_disp_bicat_of_cat_property_dfl_full_comp_cat.
  Qed.

  Definition finlim_dfl_comp_cat_counit_inv_local_property
    : disp_pstrans
        (disp_pseudo_comp
           _ _ _ _ _
           dfl_comp_cat_to_finlim_disp_psfunctor_local_property
           finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property)
        (disp_pseudo_id _)
        finlim_dfl_comp_cat_counit_inv.
  Proof.
    use make_disp_pstrans_inv_contr.
    - apply disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - apply finlim_dfl_comp_cat_counit_local_property.
    - intros.
      apply finlim_dfl_comp_cat_counit_local_property_pointwise_adjequiv.
  Qed.

  (** * 5. The displayed biequivalence *)
  Definition finlim_dfl_comp_cat_biequivalence_unit_counit_local_property
    : is_disp_biequivalence_unit_counit
        _ _
        finlim_dfl_comp_cat_biequivalence_unit_counit
        finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
        dfl_comp_cat_to_finlim_disp_psfunctor_local_property.
  Proof.
    simple refine (_ ,, _).
    - exact finlim_dfl_comp_cat_unit_local_property.
    - exact finlim_dfl_comp_cat_counit_inv_local_property.
  Defined.

  Definition finlim_biequiv_dfl_comp_cat_psfunctor_local_property
    : disp_is_biequivalence_data
        _
        _
        finlim_dfl_comp_cat_biequivalence_adjoints
        finlim_dfl_comp_cat_biequivalence_unit_counit_local_property.
  Proof.
    simple refine (_ ,, _ ,, (_ ,, _) ,, (_ ,, _)).
    - exact finlim_dfl_comp_cat_unit_inv_local_property.
    - exact finlim_dfl_comp_cat_counit_local_property.
    - use make_disp_invmodification_contr.
      + apply disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property.
      + apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    - use make_disp_invmodification_contr.
      + apply disp_2cells_iscontr_disp_bicat_of_univ_cat_with_cat_property.
      + apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
    - use make_disp_invmodification_contr.
      + apply disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat.
      + apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
    - use make_disp_invmodification_contr.
      + apply disp_2cells_iscontr_disp_bicat_of_cat_property_dfl_full_comp_cat.
      + apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  Defined.
End LocalPropertyBiequiv.
