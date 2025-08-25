(**

 The internal language of ∏-pretoposes

 In other files, we gave several extensions of the biequivalence between categories with
 finite limits and full DFL comprehension categories. Now we put these extensions together
 in order to obtain internal language theorems for several classes of toposes. The results
 are split over several files.

 In this file we consider ∏-pretoposes with a parameterized natural numbers objects. Recall
 that a pretopos is a category that is both extensive and exact. A ∏-pretopos is a locally
 Cartesian closed pretopos. To obtain the desired biequivalence, we combine the biequivalence
 for locally Cartesian closed categories and ∏-types in comprehension categories with the
 biequivalence for local properties.

 Contents
 1. The bicategory of ∏-pretoposes
 2. Accessors for ∏-pretoposes
 3. The bicategory of ∏-pretopos comprehension categories
 4. Accessors for ∏-pretopos comprehension categories
 5. The biequivalence

                                                                                          *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.ProductDispBiequiv.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.CatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Biequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.Pretopos.

Local Open Scope cat.

(** * 1. The bicategory of ∏-pretoposes *)
Definition disp_bicat_of_univ_pretopos
  : disp_bicat bicat_of_univ_cat_with_finlim
  := disp_dirprod_bicat
       (disp_bicat_of_univ_cat_with_cat_property pretopos_local_property)
       disp_bicat_univ_lccc.

Proposition disp_2cells_isaprop_disp_bicat_of_univ_pretopos
  : disp_2cells_isaprop disp_bicat_of_univ_pretopos.
Proof.
  use disp_2cells_isaprop_prod.
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
Defined.

Proposition disp_locally_groupoid_disp_bicat_of_univ_pretopos
  : disp_locally_groupoid disp_bicat_of_univ_pretopos.
Proof.
  use disp_locally_groupoid_prod.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_locally_groupoid_univ_lccc.
Defined.

Proposition disp_univalent_2_disp_bicat_of_univ_pretopos
  : disp_univalent_2 disp_bicat_of_univ_pretopos.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
  - apply disp_univalent_2_disp_bicat_univ_cat_with_cat_property.
  - exact disp_univalent_2_disp_bicat_univ_lccc.
Qed.

Proposition disp_univalent_2_0_disp_bicat_of_univ_pretopos
  : disp_univalent_2_0 disp_bicat_of_univ_pretopos.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_pretopos.
Qed.

Proposition disp_univalent_2_1_disp_bicat_of_univ_pretopos
  : disp_univalent_2_1 disp_bicat_of_univ_pretopos.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_pretopos.
Qed.

Definition bicat_of_univ_pi_pretopos
  : bicat
  := total_bicat disp_bicat_of_univ_pretopos.

Proposition is_univalent_2_bicat_of_univ_pi_pretopos
  : is_univalent_2 bicat_of_univ_pi_pretopos.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_of_univ_pretopos.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_0_bicat_of_univ_pi_pretopos
  : is_univalent_2_0 bicat_of_univ_pi_pretopos.
Proof.
  apply is_univalent_2_bicat_of_univ_pi_pretopos.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_pi_pretopos
  : is_univalent_2_1 bicat_of_univ_pi_pretopos.
Proof.
  apply is_univalent_2_bicat_of_univ_pi_pretopos.
Qed.

(** * 2. Accessors for ∏-pretoposes *)
Definition univ_pi_pretopos
  : UU
  := bicat_of_univ_pi_pretopos.

Coercion univ_pi_pretopos_to_univ_pretopos
         (E : univ_pi_pretopos)
  : univ_pretopos.
Proof.
  use make_univ_pretopos.
  - exact (pr1 E).
  - exact (pr111 (pr112 E)).
  - exact (pr1 (pr211 (pr112 E))).
  - exact (pr2 (pr211 (pr112 E))).
  - exact (pr21 (pr112 E)).
  - exact (pr112 (pr112 E)).
  - exact (pr212 (pr112 E)).
  - exact (pr22 (pr112 E)).
Defined.

Definition univ_pi_pretopos_lccc
          (E : univ_pi_pretopos)
  : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim E)
  := pr122 E.

Definition make_univ_pi_pretopos
           (E : univ_pretopos)
           (HE : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim E))
  : univ_pi_pretopos.
Proof.
  simple refine (_ ,, ((((_ ,, (_ ,, _)) ,, _) ,, ((_ ,, _) ,, _)) ,, tt) ,, (_ ,, tt)).
  - exact (pretopos_to_finlim E).
  - exact (strict_initial_univ_pretopos E).
  - exact (bincoproducts_univ_pretopos E).
  - exact (stable_bincoproducts_univ_pretopos E).
  - exact (disjoint_bincoproducts_univ_pretopos E).
  - exact (is_regular_category_coeqs_of_kernel_pair
             (is_regular_category_univ_pretopos E)).
  - exact (is_regular_category_regular_epi_pb_stable
             (is_regular_category_univ_pretopos E)).
  - exact (all_internal_eqrel_effective_univ_pretopos E).
  - exact HE.
Defined.

Definition functor_pi_pretopos
           (E₁ E₂ : univ_pi_pretopos)
  : UU
  := E₁ --> E₂.

Coercion functor_pi_pretopos_to_functor_pretopos
         {E₁ E₂ : univ_pi_pretopos}
         (F : functor_pi_pretopos E₁ E₂)
  : functor_pretopos E₁ E₂.
Proof.
  use make_functor_pretopos.
  - exact (pr1 F).
  - exact (pr11 (pr212 F)).
  - exact (pr21 (pr212 F)).
  - exact (pr12 (pr212 F)).
Defined.

Definition preserves_locally_cartesian_closed_functor_pi_pretopos
           {E₁ E₂ : univ_pi_pretopos}
           (F : functor_pi_pretopos E₁ E₂)
  : preserves_locally_cartesian_closed
      (functor_finlim_preserves_pullback F)
      (univ_pi_pretopos_lccc E₁)
      (univ_pi_pretopos_lccc E₂)
  := pr222 F.

Definition make_functor_pi_pretopos
           {E₁ E₂ : univ_pi_pretopos}
           (F : functor_pretopos E₁ E₂)
           (HF : preserves_locally_cartesian_closed
                   (functor_finlim_preserves_pullback F)
                   (univ_pi_pretopos_lccc E₁)
                   (univ_pi_pretopos_lccc E₂))
  : functor_pi_pretopos E₁ E₂.
Proof.
  simple refine (_ ,, (tt ,, ((_ ,, _) ,, (_ ,, tt))) ,, (tt ,, _)).
  - exact (functor_pretopos_to_functor_finlim F).
  - exact (preserves_initial_functor_pretopos F).
  - exact (preserves_bincoproduct_functor_pretopos F).
  - exact (preserves_regular_epi_functor_pretopos F).
  - exact HF.
Defined.

Definition nat_trans_pi_pretopos
           {E₁ E₂ : univ_pi_pretopos}
           (F G : functor_pi_pretopos E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_pi_pretopos_to_nat_trans_finlim
         {E₁ E₂ : univ_pi_pretopos}
         {F G : functor_pi_pretopos E₁ E₂}
         (τ : nat_trans_pi_pretopos F G)
  : nat_trans_finlim F G
  := pr1 τ.

Definition make_nat_trans_pi_pretopos
           {E₁ E₂ : univ_pi_pretopos}
           {F G : functor_pi_pretopos E₁ E₂}
           (τ : F ⟹ G)
  : nat_trans_pi_pretopos F G
  := make_nat_trans_finlim τ ,, (tt ,, tt) ,, (tt ,, tt).

Proposition nat_trans_pi_pretopos_eq
            {E₁ E₂ : univ_pi_pretopos}
            {F G : functor_pi_pretopos E₁ E₂}
            {τ₁ τ₂ : nat_trans_pi_pretopos F G}
            (p : ∏ (x : E₁), τ₁ x = τ₂ x)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isaproptotal2.
    - intro.
      use isapropdirprod ; apply isapropunit.
    - intros.
      use pathsdirprod ; apply isapropunit.
  }
  use nat_trans_finlim_eq.
  exact p.
Qed.

(** * 3. The bicategory of ∏-pretopos comprehension categories *)
Definition disp_bicat_univ_pi_pretopos_language
  : disp_bicat bicat_of_dfl_full_comp_cat
  := disp_dirprod_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat pretopos_local_property)
       disp_bicat_of_pi_type_dfl_full_comp_cat.

Proposition disp_2cells_isaprop_disp_bicat_univ_pi_pretopos_language
  : disp_2cells_isaprop disp_bicat_univ_pi_pretopos_language.
Proof.
  use disp_2cells_isaprop_prod.
  - apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Proposition disp_locally_groupoid_disp_bicat_univ_pi_pretopos_language
  : disp_locally_groupoid disp_bicat_univ_pi_pretopos_language.
Proof.
  use disp_locally_groupoid_prod.
  - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Proposition disp_univalent_2_disp_bicat_univ_pi_pretopos_language
  : disp_univalent_2 disp_bicat_univ_pi_pretopos_language.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_dfl_full_comp_cat.
  - apply univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact univalent_2_disp_bicat_of_pi_type_dfl_full_comp_cat.
Qed.

Proposition disp_univalent_2_0_disp_bicat_univ_pi_pretopos_language
  : disp_univalent_2_0 disp_bicat_univ_pi_pretopos_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_pi_pretopos_language.
Qed.

Proposition disp_univalent_2_1_disp_bicat_univ_pi_pretopos_language
  : disp_univalent_2_1 disp_bicat_univ_pi_pretopos_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_pi_pretopos_language.
Qed.

(** * 4. Accessors for ∏-pretopos comprehension categories *)
Definition univ_pi_pretopos_language
  : bicat
  := total_bicat disp_bicat_univ_pi_pretopos_language.

Proposition is_univalent_2_univ_pi_pretopos_language
  : is_univalent_2 univ_pi_pretopos_language.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_univ_pi_pretopos_language.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_univ_pi_pretopos_language
  : is_univalent_2_0 univ_pi_pretopos_language.
Proof.
  apply is_univalent_2_univ_pi_pretopos_language.
Qed.

Proposition is_univalent_2_1_univ_pi_pretopos_language
  : is_univalent_2_1 univ_pi_pretopos_language.
Proof.
  apply is_univalent_2_univ_pi_pretopos_language.
Qed.

Definition pi_pretopos_comp_cat
  : UU
  := univ_pi_pretopos_language.

Coercion pi_pretopos_comp_cat_to_dfl_comp_cat
         (C : pi_pretopos_comp_cat)
  : dfl_full_comp_cat
  := pr1 C.

Definition fiberwise_strict_initial_pi_pretopos_comp_cat
           (C : pi_pretopos_comp_cat)
  : fiberwise_cat_property
      strict_initial_local_property
      (pi_pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_sub_left
          (local_property_conj_left
             (pr112 C))).

Definition fiberwise_bincoproduct_pi_pretopos_comp_cat
           (C : pi_pretopos_comp_cat)
  : fiberwise_cat_property
      stable_bincoproducts_local_property
      (pi_pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_sub_left
          (local_property_conj_left
             (pr112 C))).

Definition fiberwise_regular_pi_pretopos_comp_cat
           (C : pi_pretopos_comp_cat)
  : fiberwise_cat_property
      regular_local_property
      (pi_pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left (local_property_conj_right (pr112 C)).

Definition fiberwise_effective_eqrel_pi_pretopos_comp_cat
           (C : pi_pretopos_comp_cat)
  : fiberwise_cat_property
      all_eqrel_effective_local_property
      (pi_pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right (local_property_conj_right (pr112 C)).

Definition comp_cat_dependent_prod_pi_pretopos_comp_cat
           (C : pi_pretopos_comp_cat)
  : comp_cat_dependent_prod C
  := pr122 C.

Definition pi_pretopos_comp_cat_functor
           (C₁ C₂ : pi_pretopos_comp_cat)
  : UU
  := C₁ --> C₂.

Coercion pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor
         {C₁ C₂ : pi_pretopos_comp_cat}
         (F : pi_pretopos_comp_cat_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (pi_pretopos_comp_cat_to_dfl_comp_cat C₁)
      (pi_pretopos_comp_cat_to_dfl_comp_cat C₂)
  := pr1 F.

Definition fiberwise_strict_initial_pi_pretopos_comp_cat_functor
           {C₁ C₂ : pi_pretopos_comp_cat}
           (F : pi_pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_strict_initial_pi_pretopos_comp_cat C₁)
      (fiberwise_strict_initial_pi_pretopos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_sub_left
          (local_property_functor_conj_left (pr212 F))).

Definition fiberwise_bincoproduct_pi_pretopos_comp_cat_functor
           {C₁ C₂ : pi_pretopos_comp_cat}
           (F : pi_pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_bincoproduct_pi_pretopos_comp_cat C₁)
      (fiberwise_bincoproduct_pi_pretopos_comp_cat C₂)
  := local_property_functor_conj_right
       (local_property_functor_sub_left
          (local_property_functor_conj_left (pr212 F))).

Definition fiberwise_regular_pi_pretopos_comp_cat_functor
           {C₁ C₂ : pi_pretopos_comp_cat}
           (F : pi_pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_regular_pi_pretopos_comp_cat C₁)
      (fiberwise_regular_pi_pretopos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_conj_right (pr212 F)).

Definition preserves_comp_cat_dependent_prod_pi_pretopos_comp_cat_functor
           {C₁ C₂ : pi_pretopos_comp_cat}
           (F : pi_pretopos_comp_cat_functor C₁ C₂)
  : preserves_comp_cat_dependent_prod
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (comp_cat_dependent_prod_pi_pretopos_comp_cat C₁)
      (comp_cat_dependent_prod_pi_pretopos_comp_cat C₂)
  := pr222 F.

Definition pi_pretopos_comp_cat_nat_trans
           {C₁ C₂ : pi_pretopos_comp_cat}
           (F G : pi_pretopos_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion pi_pretopos_comp_cat_nat_trans_to_dfl_full_comp_cat_nat_trans
         {C₁ C₂ : pi_pretopos_comp_cat}
         {F G : pi_pretopos_comp_cat_functor C₁ C₂}
         (τ : pi_pretopos_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (pi_pretopos_comp_cat_functor_to_dfl_comp_cat_functor G)
  := pr1 τ.

(** * 5. The biequivalence *)
Definition disp_psfunctor_lang_univ_pi_pretopos
  : disp_psfunctor
      disp_bicat_of_univ_pretopos
      disp_bicat_univ_pi_pretopos_language
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  refine (prod_disp_psfunctor
            _ _ _ _
            (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
               pretopos_local_property)
            finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types).
  - apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition lang_univ_pi_pretopos
  : psfunctor
      bicat_of_univ_pi_pretopos
      univ_pi_pretopos_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_univ_pi_pretopos.

Definition internal_language_univ_pi_pretopos
  : is_biequivalence lang_univ_pi_pretopos.
Proof.
  refine (total_is_biequivalence
            _ _ _
            (prod_disp_is_biequivalence_data
               _ _ _ _
               _ _ _ _
               _ _ _ _
               _ _ _ _
               (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
                  pretopos_local_property)
               finlim_biequiv_dfl_comp_cat_psfunctor_pi_types)).
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
Defined.
