(**

 The internal language of elementary toposes

 In other files, we gave several extensions of the biequivalence between categories with
 finite limits and full DFL comprehension categories. Now we put these extensions together
 in order to obtain internal language theorems for several classes of toposes. The results
 are split over several files.

 In this file, we consider elementary toposes. Note that there are many equivalent ways
 to define elementary toposes. The most common one is as a cartesian closed category with
 finite limits and a subobject classifier. However, here use a definition that contains more
 redundancy, but that results in a more expressive internal language. More precisely, here we
 define elementary toposes as categories that are exact, extensive, locally cartesian closed,
 and that have finite limits and a subobject classifier. Note that this definition is equivalent
 to the other one. Technically, we define these by combining a local property (subobject
 classifier, exact, extensive) with dependent products.

 Contents
 1. The bicategory of elementary toposes
 2. Accessors for elementary toposes
 3. The bicategory of elementary topos comprehension categories
 4. Accessors for elementary toposes comprehension categories
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
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.PiPretopos.

Local Open Scope cat.

(** * 1. The bicategory of elementary toposes *)
Definition disp_bicat_of_univ_topos
  : disp_bicat bicat_of_univ_cat_with_finlim
  := disp_dirprod_bicat
       (disp_bicat_of_univ_cat_with_cat_property topos_local_property)
       disp_bicat_univ_lccc.

Proposition disp_2cells_isaprop_disp_bicat_of_univ_topos
  : disp_2cells_isaprop disp_bicat_of_univ_topos.
Proof.
  use disp_2cells_isaprop_prod.
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
Defined.

Proposition disp_locally_groupoid_disp_bicat_of_univ_topos
  : disp_locally_groupoid disp_bicat_of_univ_topos.
Proof.
  use disp_locally_groupoid_prod.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_locally_groupoid_univ_lccc.
Defined.

Proposition disp_univalent_2_disp_bicat_of_univ_topos
  : disp_univalent_2 disp_bicat_of_univ_topos.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
  - apply disp_univalent_2_disp_bicat_univ_cat_with_cat_property.
  - exact disp_univalent_2_disp_bicat_univ_lccc.
Qed.

Proposition disp_univalent_2_0_disp_bicat_of_univ_topos
  : disp_univalent_2_0 disp_bicat_of_univ_topos.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_topos.
Qed.

Proposition disp_univalent_2_1_disp_bicat_of_univ_topos
  : disp_univalent_2_1 disp_bicat_of_univ_topos.
Proof.
  apply disp_univalent_2_disp_bicat_of_univ_topos.
Qed.

Definition bicat_of_univ_topos
  : bicat
  := total_bicat disp_bicat_of_univ_topos.

Proposition is_univalent_2_bicat_of_univ_topos
  : is_univalent_2 bicat_of_univ_topos.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_of_univ_topos.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_0_bicat_of_univ_topos
  : is_univalent_2_0 bicat_of_univ_topos.
Proof.
  apply is_univalent_2_bicat_of_univ_topos.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_topos
  : is_univalent_2_1 bicat_of_univ_topos.
Proof.
  apply is_univalent_2_bicat_of_univ_topos.
Qed.

(** * 2. Accessors for elementary toposes *)
Definition univ_topos
  : UU
  := bicat_of_univ_topos.

Coercion univ_topos_to_univ_pretopos
         (E : univ_topos)
  : univ_pretopos.
Proof.
  use make_univ_pretopos.
  - exact (pr1 E).
  - exact (pr1 (pr111 (pr112 E))).
  - exact (pr12 (pr111 (pr112 E))).
  - exact (pr22 (pr111 (pr112 E))).
  - exact (pr211 (pr112 E)).
  - exact (pr1 (pr121 (pr112 E))).
  - exact (pr2 (pr121 (pr112 E))).
  - exact (pr221 (pr112 E)).
Defined.

Definition univ_topos_subobject_classifier
           (E : univ_topos)
  : subobject_classifier (terminal_univ_cat_with_finlim E)
  := pr2 (pr112 E).

Definition is_locally_cartesian_closed_univ_topos
           (E : univ_topos)
  : is_locally_cartesian_closed (pullbacks_univ_cat_with_finlim E)
  := pr122 E.

Definition make_univ_topos
           (E : univ_pi_pretopos)
           (Ω : subobject_classifier (terminal_univ_cat_with_finlim E))
  : univ_topos.
Proof.
  simple refine (_ ,, (((((_ ,, _ ,, _) ,, _) ,, ((_ ,, _) ,, _)) ,, _) ,, tt) ,, _ ,, tt).
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
  - exact Ω.
  - exact (univ_pi_pretopos_lccc E).
Defined.

Definition functor_topos
           (E₁ E₂ : univ_topos)
  : UU
  := E₁ --> E₂.

Coercion functor_topos_to_functor_pretopos
         {E₁ E₂ : univ_topos}
         (F : functor_topos E₁ E₂)
  : functor_pretopos E₁ E₂.
Proof.
  use make_functor_pretopos.
  - exact (pr1 F).
  - exact (pr111 (pr212 F)).
  - exact (pr211 (pr212 F)).
  - exact (pr121 (pr212 F)).
Defined.

Definition preserves_subobject_classifier_functor_topos
           {E₁ E₂ : univ_topos}
           (F : functor_topos E₁ E₂)
  : preserves_subobject_classifier
      F
      (terminal_univ_cat_with_finlim E₁)
      (terminal_univ_cat_with_finlim E₂)
      (functor_finlim_preserves_terminal F)
  := pr2 (pr212 F).

Definition preserves_locally_cartesian_closed_functor_topos
           {E₁ E₂ : univ_topos}
           (F : functor_topos E₁ E₂)
  : preserves_locally_cartesian_closed
      (functor_finlim_preserves_pullback F)
      (is_locally_cartesian_closed_univ_topos E₁)
      (is_locally_cartesian_closed_univ_topos E₂)
  := pr222 F.

Definition make_functor_topos
           {E₁ E₂ : univ_topos}
           (F : functor_pretopos E₁ E₂)
           (HF : preserves_subobject_classifier
                   F
                   (terminal_univ_cat_with_finlim E₁)
                   (terminal_univ_cat_with_finlim E₂)
                   (functor_finlim_preserves_terminal F))
           (HF' : preserves_locally_cartesian_closed
                    (functor_finlim_preserves_pullback F)
                    (is_locally_cartesian_closed_univ_topos E₁)
                    (is_locally_cartesian_closed_univ_topos E₂))
  : functor_topos E₁ E₂.
Proof.
  simple refine (_ ,, (tt ,, ((_ ,, _) ,, (_ ,, tt)) ,, _) ,, tt ,, _).
  - exact (functor_pretopos_to_functor_finlim F).
  - exact (preserves_initial_functor_pretopos F).
  - exact (preserves_bincoproduct_functor_pretopos F).
  - exact (preserves_regular_epi_functor_pretopos F).
  - exact HF.
  - exact HF'.
Defined.

Definition nat_trans_topos
           {E₁ E₂ : univ_topos}
           (F G : functor_topos E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_topos_to_nat_trans_finlim
         {E₁ E₂ : univ_topos}
         {F G : functor_topos E₁ E₂}
         (τ : nat_trans_topos F G)
  : nat_trans_finlim F G
  := pr1 τ.

Definition make_nat_trans_topos
           {E₁ E₂ : univ_topos}
           {F G : functor_topos E₁ E₂}
           (τ : F ⟹ G)
  : nat_trans_topos F G
  := make_nat_trans_finlim τ ,, (tt ,, tt) ,, (tt ,, tt).

Proposition nat_trans_topos_eq
            {E₁ E₂ : univ_topos}
            {F G : functor_topos E₁ E₂}
            {τ₁ τ₂ : nat_trans_topos F G}
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

(** * 3. The bicategory of elementary topos comprehension categories *)
Definition disp_bicat_univ_topos_language
  : disp_bicat bicat_of_dfl_full_comp_cat
  := disp_dirprod_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat topos_local_property)
       disp_bicat_of_pi_type_dfl_full_comp_cat.

Proposition disp_2cells_isaprop_disp_bicat_univ_topos_language
  : disp_2cells_isaprop disp_bicat_univ_topos_language.
Proof.
  use disp_2cells_isaprop_prod.
  - apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Proposition disp_locally_groupoid_disp_bicat_univ_topos_language
  : disp_locally_groupoid disp_bicat_univ_topos_language.
Proof.
  use disp_locally_groupoid_prod.
  - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Proposition disp_univalent_2_disp_bicat_univ_topos_language
  : disp_univalent_2 disp_bicat_univ_topos_language.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact is_univalent_2_1_bicat_of_dfl_full_comp_cat.
  - apply univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact univalent_2_disp_bicat_of_pi_type_dfl_full_comp_cat.
Qed.

Proposition disp_univalent_2_0_disp_bicat_univ_topos_language
  : disp_univalent_2_0 disp_bicat_univ_topos_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_language.
Qed.

Proposition disp_univalent_2_1_disp_bicat_univ_topos_language
  : disp_univalent_2_1 disp_bicat_univ_topos_language.
Proof.
  apply disp_univalent_2_disp_bicat_univ_topos_language.
Qed.

Definition univ_topos_language
  : bicat
  := total_bicat disp_bicat_univ_topos_language.

Proposition is_univalent_2_univ_topos_language
  : is_univalent_2 univ_topos_language.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_univ_topos_language.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_univ_topos_language
  : is_univalent_2_0 univ_topos_language.
Proof.
  apply is_univalent_2_univ_topos_language.
Qed.

Proposition is_univalent_2_1_univ_topos_language
  : is_univalent_2_1 univ_topos_language.
Proof.
  apply is_univalent_2_univ_topos_language.
Qed.

(** * 4. Accessors for elementary toposes comprehension categories *)
Definition topos_comp_cat
  : UU
  := univ_topos_language.

Coercion topos_comp_cat_to_dfl_comp_cat
         (C : topos_comp_cat)
  : dfl_full_comp_cat
  := pr1 C.

Definition fiberwise_strict_initial_topos_comp_cat
           (C : topos_comp_cat)
  : fiberwise_cat_property
      strict_initial_local_property
      (topos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (pr112 C)))).

Definition fiberwise_bincoproduct_topos_comp_cat
           (C : topos_comp_cat)
  : fiberwise_cat_property
      stable_bincoproducts_local_property
      (topos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (pr112 C)))).

Definition fiberwise_regular_topos_comp_cat
           (C : topos_comp_cat)
  : fiberwise_cat_property
      regular_local_property
      (topos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_conj_right
          (local_property_conj_left (pr112 C))).

Definition fiberwise_effective_eqrel_topos_comp_cat
           (C : topos_comp_cat)
  : fiberwise_cat_property
      all_eqrel_effective_local_property
      (topos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_conj_right
          (local_property_conj_left (pr112 C))).

Definition fiberwise_subobject_classifier_topos_comp_cat
           (C : topos_comp_cat)
  : fiberwise_cat_property
      subobject_classifier_local_property
      (topos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right (pr112 C).

Definition comp_cat_dependent_prod_topos_comp_cat
           (C : topos_comp_cat)
  : comp_cat_dependent_prod C
  := pr122 C.

Definition topos_comp_cat_functor
           (C₁ C₂ : topos_comp_cat)
  : UU
  := C₁ --> C₂.

Coercion topos_comp_cat_functor_to_dfl_comp_cat_functor
         {C₁ C₂ : topos_comp_cat}
         (F : topos_comp_cat_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (topos_comp_cat_to_dfl_comp_cat C₁)
      (topos_comp_cat_to_dfl_comp_cat C₂)
  := pr1 F.

Definition fiberwise_strict_initial_topos_comp_cat_functor
           {C₁ C₂ : topos_comp_cat}
           (F : topos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_strict_initial_topos_comp_cat C₁)
      (fiberwise_strict_initial_topos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left (pr212 F)))).

Definition fiberwise_bincoproduct_topos_comp_cat_functor
           {C₁ C₂ : topos_comp_cat}
           (F : topos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_bincoproduct_topos_comp_cat C₁)
      (fiberwise_bincoproduct_topos_comp_cat C₂)
  := local_property_functor_conj_right
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left (pr212 F)))).

Definition fiberwise_regular_topos_comp_cat_functor
           {C₁ C₂ : topos_comp_cat}
           (F : topos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_regular_topos_comp_cat C₁)
      (fiberwise_regular_topos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_conj_right
          (local_property_functor_conj_left (pr212 F))).

Definition fiberwise_subobject_classifier_topos_comp_cat_functor
           {C₁ C₂ : topos_comp_cat}
           (F : topos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_subobject_classifier_topos_comp_cat C₁)
      (fiberwise_subobject_classifier_topos_comp_cat C₂)
  := local_property_functor_conj_right (pr212 F).

Definition preserves_comp_cat_dependent_prod_topos_comp_cat_functor
           {C₁ C₂ : topos_comp_cat}
           (F : topos_comp_cat_functor C₁ C₂)
  : preserves_comp_cat_dependent_prod
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (comp_cat_dependent_prod_topos_comp_cat C₁)
      (comp_cat_dependent_prod_topos_comp_cat C₂)
  := pr222 F.

Definition topos_comp_cat_nat_trans
           {C₁ C₂ : topos_comp_cat}
           (F G : topos_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion topos_comp_cat_nat_trans_to_dfl_full_comp_cat_nat_trans
         {C₁ C₂ : topos_comp_cat}
         {F G : topos_comp_cat_functor C₁ C₂}
         (τ : topos_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans
      (topos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (topos_comp_cat_functor_to_dfl_comp_cat_functor G)
  := pr1 τ.

(** * 5. The biequivalence *)
Definition disp_psfunctor_lang_univ_topos
  : disp_psfunctor
      disp_bicat_of_univ_topos
      disp_bicat_univ_topos_language
      finlim_biequiv_dfl_comp_cat_psfunctor.
Proof.
  refine (prod_disp_psfunctor
            _ _ _ _
            (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
               topos_local_property)
            finlim_biequiv_dfl_comp_cat_disp_psfunctor_pi_types).
  - apply disp_2cells_isaprop_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - apply disp_locally_groupoid_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition lang_univ_topos
  : psfunctor
      bicat_of_univ_topos
      univ_topos_language
  := total_psfunctor
       _ _ _
       disp_psfunctor_lang_univ_topos.

Definition internal_language_univ_topos
  : is_biequivalence lang_univ_topos.
Proof.
  refine (total_is_biequivalence
            _ _ _
            (prod_disp_is_biequivalence_data
               _ _ _ _
               _ _ _ _
               _ _ _ _
               _ _ _ _
               (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
                  topos_local_property)
               finlim_biequiv_dfl_comp_cat_psfunctor_pi_types)).
  - apply disp_2cells_isaprop_disp_bicat_of_univ_cat_with_cat_property.
  - apply disp_locally_groupoid_disp_bicat_of_univ_cat_with_cat_property.
  - exact disp_2cells_isaprop_univ_lccc.
  - exact disp_locally_groupoid_univ_lccc.
Defined.
