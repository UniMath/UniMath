(******************************************************************************************

 The biequivalence for pi-types

 In this file, we extend the biequivalence between categories with finite limits and full
 DFL comprehension to locally Cartesian closed categories and full DFL comprehension
 categories that support pi-types. This was one of the results by Clairambault and Dybjer.

 Other files in this directory contain extensions of this biequivalence to local properties
 (e.g., exactness, extensiveness, and being a pretopos) and to subobject classifiers. All of
 these constructions are very similar and they follow the same steps and ideas: one extends
 the pseudofunctors, unit, and counit using displayed machinery.

 For each of these constructions, univalence plays a very important role. The reason for that
 is because in various steps in the construction one needs to transport structure/property
 along an equivalence. Let us see why this is so crucial in the proof. Whenever we have a
 full DFL comprehension category `C`, then, using democracy, we can show this comprehension
 category is actually equivalent to the arrow category of the category of contexts of `C`.
 If we assume that `C` has some additional structure or satisfies some properties, then we
 transport this along the equivalence to acquire the same structure/properties for the
 arrow category on `C`, and this is what gives us the desired structure/properties on `C`.
 For this reason, each of these constructions frequently uses induction on equivalence to
 transport structures and properties.

 References
 - "The biequivalence of locally cartesian closed categories and Martin-Löf type theories" by
   Clairambault and Dybjer

 Contents
 1. Lemmas on equivalences and locally cartesian closed categories
 2. The extended pseudofunctor from categories to comprehension categories
 3. The extended pseudofunctor from comprehension categories to categories
 4. The unit
 5. The counit
 6. The displayed biequivalence

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
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
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudoNaturalAdjequiv.
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
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Lemmas on equivalences and locally cartesian closed categories *)
Proposition id_preserves_locally_cartesian_closed'
            {C : univalent_category}
            {PB₁ : Pullbacks C}
            {PB₂ : Pullbacks C}
            (FPB : preserves_pullback (functor_identity C))
            (P₁ : is_locally_cartesian_closed PB₁)
            (P₂ : is_locally_cartesian_closed PB₂)
  : preserves_locally_cartesian_closed FPB P₁ P₂.
Proof.
  assert (PB₁ = PB₂) as q.
  {
    apply isaprop_Pullbacks.
    apply univalent_category_is_univalent.
  }
  induction q.
  assert (identity_preserves_pullback _ = FPB) as q.
  {
    apply isaprop_preserves_pullback.
  }
  induction q.
  assert (P₁ = P₂) as q.
  {
    apply isaprop_is_locally_cartesian_closed.
  }
  induction q.
  apply id_preserves_locally_cartesian_closed.
Qed.

Definition has_dependent_products_adj_equiv_f_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           (P : comp_cat_dependent_prod C₁)
  : comp_cat_dependent_prod C₂.
Proof.
  revert C₁ C₂ F P.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C P.
  exact P.
Qed.

Definition has_dependent_products_adj_equiv_f
           {C₁ C₂ : dfl_full_comp_cat}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : left_adjoint_equivalence F)
           (P : comp_cat_dependent_prod C₁)
  : comp_cat_dependent_prod C₂.
Proof.
  exact (has_dependent_products_adj_equiv_f_help (F ,, HF) P).
Qed.

Definition preserves_dependent_products_adj_equiv_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           (F' := pr1 F : dfl_full_comp_cat_functor C₁ C₂)
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
  : preserves_comp_cat_dependent_prod F' P₁ P₂.
Proof.
  unfold F' ; clear F'.
  revert C₁ C₂ F P₁ P₂.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C P₁ P₂.
  assert (P₁ = P₂) as q.
  {
    apply isaprop_comp_cat_dependent_prod.
  }
  induction q.
  exact (id_preserves_comp_cat_dependent_prod _ _).
Qed.

Definition preserves_dependent_products_adj_equiv
           {C₁ C₂ : dfl_full_comp_cat}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : left_adjoint_equivalence F)
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
  : preserves_comp_cat_dependent_prod F P₁ P₂.
Proof.
  exact (preserves_dependent_products_adj_equiv_help (F ,, HF) P₁ P₂).
Qed.

Definition preserves_dependent_products_inv2cell
           {C D : dfl_full_comp_cat}
           {PC : comp_cat_dependent_prod C}
           {PD : comp_cat_dependent_prod D}
           (F G : dfl_full_comp_cat_functor C D)
           (τ : invertible_2cell G F)
           (HF : preserves_comp_cat_dependent_prod F PC PD)
  : preserves_comp_cat_dependent_prod G PC PD.
Proof.
  revert C D G F τ PC PD HF.
  use J_2_1.
  {
    exact is_univalent_2_1_bicat_of_dfl_full_comp_cat.
  }
  intros C D F PC PD HF.
  exact HF.
Qed.

Definition preserves_dependent_products_adj_equiv_inv2cell_help
           {C₁ C₂ D₁ D₂ : dfl_full_comp_cat}
           {PC₁ : comp_cat_dependent_prod C₁}
           {PC₂ : comp_cat_dependent_prod C₂}
           {PD₁ : comp_cat_dependent_prod D₁}
           {PD₂ : comp_cat_dependent_prod D₂}
           (F : dfl_full_comp_cat_functor C₁ D₁)
           (G : dfl_full_comp_cat_functor C₂ D₂)
           (EC : adjoint_equivalence C₁ C₂)
           (ED : adjoint_equivalence D₁ D₂)
           (τ : invertible_2cell (pr1 EC · G) (F · pr1 ED))
           (HF : preserves_comp_cat_dependent_prod F PC₁ PD₁)
  : preserves_comp_cat_dependent_prod G PC₂ PD₂.
Proof.
  revert C₁ C₂ EC D₁ D₂ ED F G τ PC₁ PC₂ PD₁ PD₂ HF.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros C.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  }
  intros D F G τ PC₁ PC₂ PD₁ PD₂ HF.
  assert (PC₁ = PC₂) as q.
  {
    apply isaprop_comp_cat_dependent_prod.
  }
  induction q.
  assert (PD₁ = PD₂) as q.
  {
    apply isaprop_comp_cat_dependent_prod.
  }
  induction q.
  use preserves_dependent_products_inv2cell.
  - exact F.
  - exact (comp_of_invertible_2cell
             (linvunitor_invertible_2cell _)
             (comp_of_invertible_2cell
                τ
                (runitor_invertible_2cell _))).
  - exact HF.
Qed.

Definition preserves_dependent_products_adj_equiv_inv2cell
           {C₁ C₂ D₁ D₂ : dfl_full_comp_cat}
           {PC₁ : comp_cat_dependent_prod C₁}
           {PC₂ : comp_cat_dependent_prod C₂}
           {PD₁ : comp_cat_dependent_prod D₁}
           {PD₂ : comp_cat_dependent_prod D₂}
           (F : dfl_full_comp_cat_functor C₁ D₁)
           (G : dfl_full_comp_cat_functor C₂ D₂)
           {EC : C₁ --> C₂}
           (HEC : left_adjoint_equivalence EC)
           {ED : D₁ --> D₂}
           (HED : left_adjoint_equivalence ED)
           (τ : invertible_2cell (EC · G) (F · ED))
           (HF : preserves_comp_cat_dependent_prod F PC₁ PD₁)
  : preserves_comp_cat_dependent_prod G PC₂ PD₂.
Proof.
  exact (preserves_dependent_products_adj_equiv_inv2cell_help
           F G
           (EC ,, HEC) (ED ,, HED)
           τ
           HF).
Qed.

(** * 2. The extended pseudofunctor from categories to comprehension categories *)
Definition finlim_comp_cat_dependent_prod
           (C : univ_cat_with_finlim)
           (H : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim C))
  : comp_cat_dependent_prod (finlim_to_comp_cat C).
Proof.
  use make_comp_cat_dependent_prod_all.
  apply cod_dependent_products.
  exact H.
Defined.

Definition finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_univ_lccc
      disp_bicat_of_pi_type_dfl_full_comp_cat
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, _ ,, tt).
    exact (finlim_comp_cat_dependent_prod C (pr1 H)).
  - abstract
      (refine (λ C₁ C₂ F P₁ P₂ HF, tt ,, _) ; simpl ;
       use preserves_comp_cat_dependent_prod_all ;
       exact (pr2 HF)).
Defined.

(** * 3. The extended pseudofunctor from comprehension categories to categories *)
Definition dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob
           (C : dfl_full_comp_cat)
           (P : comp_cat_dependent_prod C)
  : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim (dfl_full_comp_cat_to_finlim C)).
Proof.
  use dfl_full_comp_cat_mor_ind.
  intros Γ A ; simpl.
  refine (is_left_adjoint_equivalence
            _ _ _ _
            (fiber_functor_natural_nat_z_iso _ _ (comp_cat_comprehension C) (π A))
            (fiber_functor_comprehension_adj_equiv _ _)
            (fiber_functor_comprehension_adj_equiv _ _)
            (pr1 P Γ A)).
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply is_univalent_cod_slice.
  - apply is_univalent_cod_slice.
Qed.

Definition dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_mor
           {C₁ C₂ : dfl_full_comp_cat}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
           (HF : preserves_comp_cat_dependent_prod F P₁ P₂)
  : preserves_locally_cartesian_closed
      (functor_finlim_preserves_pullback (dfl_functor_comp_cat_to_finlim_functor F))
      (dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob C₁ P₁)
      (dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob C₂ P₂).
Proof.
  assert (comp_cat_dependent_prod
            (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₁)))
    as P₁'.
  {
    use finlim_comp_cat_dependent_prod.
    apply dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob.
    exact P₁.
  }
  assert (comp_cat_dependent_prod
            (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₂)))
    as P₂'.
  {
    use finlim_comp_cat_dependent_prod.
    apply dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob.
    exact P₂.
  }
  pose proof (preserves_dependent_products_adj_equiv_inv2cell
                F
                (finlim_to_dfl_comp_cat_functor (dfl_functor_comp_cat_to_finlim_functor F))
                (finlim_dfl_comp_cat_counit_pointwise_equiv C₁)
                (finlim_dfl_comp_cat_counit_pointwise_equiv C₂)
                (psnaturality_of finlim_dfl_comp_cat_counit F)
                HF
                (PC₂ := P₁')
                (PD₂ := P₂'))
    as HF'.
  use dfl_full_comp_cat_mor_ind.
  intros Γ A B.
  use (preserves_comp_cat_dependent_prod_all_lemma _ _ _ _ (HF' Γ _ B)).
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - apply is_univalent_cod_slice.
  - apply is_univalent_cod_slice.
Qed.

Definition dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_of_pi_type_dfl_full_comp_cat
      disp_bicat_univ_lccc
      dfl_comp_cat_to_finlim_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - refine (λ C P, _ ,, tt).
    exact (dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob C (pr1 P)).
  - intros C₁ C₂ F P₁ P₂ HF.
    refine (tt ,, _).
    exact (dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_mor _ _ (pr2 HF)).
Qed.

(** * 4. The unit *)
Definition finlim_dfl_comp_cat_unit_pi_types
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_unit.
Proof.
  use make_disp_pstrans_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - intros C H.
    refine (tt ,, _).
    apply id_preserves_locally_cartesian_closed'.
Qed.

(** * 5. The counit *)
Definition finlim_dfl_comp_cat_counit_pi_types
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types)
      finlim_dfl_comp_cat_counit.
Proof.
  use make_disp_pstrans_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, tt ,, _).
    apply (preserves_dependent_products_adj_equiv
             (finlim_dfl_comp_cat_counit_pointwise_equiv C)).
Qed.

(** * 6. The displayed biequivalence *)
Definition finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types
  : is_disp_biequivalence_unit_counit
      _ _
      finlim_dfl_comp_cat_biequivalence_unit_counit
      finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
      dfl_comp_cat_to_finlim_disp_psfunctor_pi_types.
Proof.
  use make_disp_biequiv_unit_counit_pointwise_adjequiv_alt.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
  - exact finlim_dfl_comp_cat_biequivalence_adjoints.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact finlim_dfl_comp_cat_unit_pi_types.
  - exact finlim_dfl_comp_cat_counit_pi_types.
  - intros x xx.
    use disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition finlim_biequiv_dfl_comp_cat_psfunctor_pi_types
  : disp_is_biequivalence_data
      _
      _
      finlim_dfl_comp_cat_biequivalence_adjoints
      finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types.
Proof.
  use (make_disp_biequiv_pointwise_adjequiv_alt _ _).
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - intros x xx.
    use disp_adjoint_equiv_disp_bicat_univ_lccc.
Defined.
