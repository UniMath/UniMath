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
           (P : has_dependent_products (cleaving_of_types C₁))
  : has_dependent_products (cleaving_of_types C₂).
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
           (P : has_dependent_products (cleaving_of_types C₁))
  : has_dependent_products (cleaving_of_types C₂).
Proof.
  exact (has_dependent_products_adj_equiv_f_help (F ,, HF) P).
Qed.

Definition preserves_dependent_products_adj_equiv_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           (F' := pr1 F : dfl_full_comp_cat_functor C₁ C₂)
           (P₁ : has_dependent_products (cleaving_of_types C₁))
           (P₂ : has_dependent_products (cleaving_of_types C₂))
  : preserves_dependent_products (cartesian_comp_cat_type_functor F') P₁ P₂.
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
    apply isaprop_has_dependent_products.
  }
  induction q.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (id_preserves_dependent_products _)).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  apply idpath.
Qed.

Definition preserves_dependent_products_adj_equiv
           {C₁ C₂ : dfl_full_comp_cat}
           {F : dfl_full_comp_cat_functor C₁ C₂}
           (HF : left_adjoint_equivalence F)
           (P₁ : has_dependent_products (cleaving_of_types C₁))
           (P₂ : has_dependent_products (cleaving_of_types C₂))
  : preserves_dependent_products (cartesian_comp_cat_type_functor F) P₁ P₂.
Proof.
  exact (preserves_dependent_products_adj_equiv_help (F ,, HF) P₁ P₂).
Qed.

Definition preserves_dependent_products_inv2cell
           {C D : dfl_full_comp_cat}
           {PC : has_dependent_products (cleaving_of_types C)}
           {PD : has_dependent_products (cleaving_of_types D)}
           (F G : dfl_full_comp_cat_functor C D)
           (τ : invertible_2cell G F)
           (HF : preserves_dependent_products (cartesian_comp_cat_type_functor F) PC PD)
  : preserves_dependent_products (cartesian_comp_cat_type_functor G) PC PD.
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
           {PC₁ : has_dependent_products (cleaving_of_types C₁)}
           {PC₂ : has_dependent_products (cleaving_of_types C₂)}
           {PD₁ : has_dependent_products (cleaving_of_types D₁)}
           {PD₂ : has_dependent_products (cleaving_of_types D₂)}
           (F : dfl_full_comp_cat_functor C₁ D₁)
           (G : dfl_full_comp_cat_functor C₂ D₂)
           (EC : adjoint_equivalence C₁ C₂)
           (ED : adjoint_equivalence D₁ D₂)
           (τ : invertible_2cell (pr1 EC · G) (F · pr1 ED))
           (HF : preserves_dependent_products (cartesian_comp_cat_type_functor F) PC₁ PD₁)
  : preserves_dependent_products (cartesian_comp_cat_type_functor G) PC₂ PD₂.
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
    apply isaprop_has_dependent_products.
  }
  induction q.
  assert (PD₁ = PD₂) as q.
  {
    apply isaprop_has_dependent_products.
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
           {PC₁ : has_dependent_products (cleaving_of_types C₁)}
           {PC₂ : has_dependent_products (cleaving_of_types C₂)}
           {PD₁ : has_dependent_products (cleaving_of_types D₁)}
           {PD₂ : has_dependent_products (cleaving_of_types D₂)}
           (F : dfl_full_comp_cat_functor C₁ D₁)
           (G : dfl_full_comp_cat_functor C₂ D₂)
           {EC : C₁ --> C₂}
           (HEC : left_adjoint_equivalence EC)
           {ED : D₁ --> D₂}
           (HED : left_adjoint_equivalence ED)
           (τ : invertible_2cell (EC · G) (F · ED))
           (HF : preserves_dependent_products (cartesian_comp_cat_type_functor F) PC₁ PD₁)
  : preserves_dependent_products (cartesian_comp_cat_type_functor G) PC₂ PD₂.
Proof.
  exact (preserves_dependent_products_adj_equiv_inv2cell_help
           F G
           (EC ,, HEC) (ED ,, HED)
           τ
           HF).
Qed.

(** * 2. The extended pseudofunctor from categories to comprehension categories *)
Definition finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_univ_lccc
      disp_bicat_of_pi_type_dfl_full_comp_cat
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, _ ,, tt).
    apply cod_dependent_products.
    exact (pr1 H).
  - refine (λ C₁ C₂ F P₁ P₂ HF, _).
    exact HF.
Defined.

(** * 3. The extended pseudofunctor from comprehension categories to categories *)
Definition dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
  : disp_psfunctor
      disp_bicat_of_pi_type_dfl_full_comp_cat
      disp_bicat_univ_lccc
      dfl_comp_cat_to_finlim_psfunctor.
Proof.
  use make_disp_psfunctor_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - refine (λ C P, _ ,, tt).
    exact (pr1 (has_dependent_products_adj_equiv_f
                  (finlim_dfl_comp_cat_counit_pointwise_equiv C)
                  (pr1 P))).
  - intros C₁ C₂ F P₁ P₂ HF.
    refine (tt ,, _).
    simpl.
    use (preserves_dependent_products_adj_equiv_inv2cell
           F
           (finlim_to_dfl_comp_cat_functor (dfl_functor_comp_cat_to_finlim_functor F))
           (finlim_dfl_comp_cat_counit_pointwise_equiv C₁)
           (finlim_dfl_comp_cat_counit_pointwise_equiv C₂)).
    + exact (pr1 P₁).
    + exact (pr1 P₂).
    + exact (psnaturality_of finlim_dfl_comp_cat_counit F).
    + exact (pr2 HF).
Defined.

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
  - exact disp_locally_groupoid_univ_lccc.
  - intros C H.
    refine (tt ,, _).
    apply id_preserves_locally_cartesian_closed'.
Qed.

Definition finlim_dfl_comp_cat_unit_pi_types_pointwise_adjequiv
           {C : univ_cat_with_finlim}
           (HC : disp_bicat_univ_lccc C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_unit_pointwise_equiv C)
      (finlim_dfl_comp_cat_unit_pi_types C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_univ_lccc.
Qed.

Definition finlim_dfl_comp_cat_unit_inv_pi_types
  : disp_pstrans
      (disp_pseudo_id _)
      (disp_pseudo_comp
         _ _ _ _ _
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types)
      finlim_dfl_comp_cat_unit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - exact disp_2cells_iscontr_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
  - apply finlim_dfl_comp_cat_unit_pi_types.
  - intros.
    apply finlim_dfl_comp_cat_unit_pi_types_pointwise_adjequiv.
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
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - refine (λ C H, tt ,, _).
    apply (preserves_dependent_products_adj_equiv
             (finlim_dfl_comp_cat_counit_pointwise_equiv C)).
Qed.

Definition finlim_dfl_comp_cat_counit_pi_types_pointwise_adjequiv
           {C : dfl_full_comp_cat}
           (HC : disp_bicat_of_pi_type_dfl_full_comp_cat C)
  : disp_left_adjoint_equivalence
      (finlim_dfl_comp_cat_counit_pointwise_equiv C)
      (finlim_dfl_comp_cat_counit_pi_types C HC).
Proof.
  use disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat.
Qed.

Definition finlim_dfl_comp_cat_counit_inv_pi_types
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         dfl_comp_cat_to_finlim_disp_psfunctor_pi_types
         finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types)
      (disp_pseudo_id _)
      finlim_dfl_comp_cat_counit_inv.
Proof.
  use make_disp_pstrans_inv_contr.
  - apply disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - apply finlim_dfl_comp_cat_counit_pi_types.
  - intros.
    apply finlim_dfl_comp_cat_counit_pi_types_pointwise_adjequiv.
Qed.

(** * 6. The displayed biequivalence *)
Definition finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types
  : is_disp_biequivalence_unit_counit
      _ _
      finlim_dfl_comp_cat_biequivalence_unit_counit
      finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types
      dfl_comp_cat_to_finlim_disp_psfunctor_pi_types.
Proof.
  simple refine (_ ,, _).
  - exact finlim_dfl_comp_cat_unit_pi_types.
  - exact finlim_dfl_comp_cat_counit_inv_pi_types.
Defined.

Definition finlim_biequiv_dfl_comp_cat_psfunctor_pi_types
  : disp_is_biequivalence_data
      _
      _
      finlim_dfl_comp_cat_biequivalence_adjoints
      finlim_dfl_comp_cat_biequivalence_unit_counit_pi_types.
Proof.
  simple refine (_ ,, _ ,, (_ ,, _) ,, (_ ,, _)).
  - exact finlim_dfl_comp_cat_unit_inv_pi_types.
  - exact finlim_dfl_comp_cat_counit_pi_types.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_univ_lccc.
    + exact disp_locally_groupoid_univ_lccc.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_univ_lccc.
    + exact disp_locally_groupoid_univ_lccc.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - use make_disp_invmodification_contr.
    + exact disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat.
    + exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.
