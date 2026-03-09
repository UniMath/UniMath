(**

 The internal language of pretoposes with a parameterized natural numbers object

 In other files, we gave several extensions of the biequivalence between categories with
 finite limits and full DFL comprehension categories. Now we put these extensions together
 in order to obtain internal language theorems for several classes of toposes. The results
 are split over several files.

 In this file we consider pretoposes with a parameterized natural numbers objects. Recall
 that a pretopos is a category that is both extensive and exact. Note that we use parameterized
 natural number objects rather than ordinary ones, since the parameterized notion is stronger
 than the ordinary one in the absence of exponentials. We can define such pretoposes using
 a local property, which allows us to extend the biequivalence directly.

 Contents
 1. The bicategory of pretoposes with natural numbers
 2. Accessors for pretoposes with natural numbers
 3. The bicategory of pretopos comprehension categories with natural numbers
 4. Accessors for pretopos comprehension categories with natural numbers
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
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
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
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.InternalLanguageTopos.Pretopos.

Local Open Scope cat.

(** * 1. The bicategory of pretoposes with natural numbers *)
Definition bicat_of_univ_pretopos_with_nat
  : bicat
  := total_bicat
       (disp_bicat_of_univ_cat_with_cat_property
          pretopos_with_nat_local_property).

Proposition is_univalent_2_bicat_of_univ_pretopos_with_nat
  : is_univalent_2 bicat_of_univ_pretopos_with_nat.
Proof.
  use total_is_univalent_2.
  - apply disp_univalent_2_disp_bicat_univ_cat_with_cat_property.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_0_bicat_of_univ_pretopos_with_nat
  : is_univalent_2_0 bicat_of_univ_pretopos_with_nat.
Proof.
  apply is_univalent_2_bicat_of_univ_pretopos_with_nat.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_pretopos_with_nat
  : is_univalent_2_1 bicat_of_univ_pretopos_with_nat.
Proof.
  apply is_univalent_2_bicat_of_univ_pretopos_with_nat.
Qed.

(** * 2. Accessors for pretoposes with natural numbers *)
Definition univ_pretopos_nat
  : UU
  := bicat_of_univ_pretopos_with_nat.

Coercion univ_pretopos_nats_to_univ_pretopos
         (E : univ_pretopos_nat)
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

Definition univ_pretopos_nat_pnno
          (E : univ_pretopos_nat)
  : parameterized_NNO
      (terminal_univ_cat_with_finlim E)
      (binproducts_univ_cat_with_finlim E)
  := pr212 E.

Definition make_univ_pretopos_nat
           (E : univ_pretopos)
           (HE : parameterized_NNO
                   (terminal_univ_cat_with_finlim E)
                   (binproducts_univ_cat_with_finlim E))
  : univ_pretopos_nat.
Proof.
  simple refine (_ ,, (((((_ ,, (_ ,, _)) ,, _) ,, ((_ ,, _) ,, _)) ,, _) ,, tt)).
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

Definition functor_pretopos_nat
           (E₁ E₂ : univ_pretopos_nat)
  : UU
  := E₁ --> E₂.

Coercion functor_pretopos_nat_to_functor_pretopos
         {E₁ E₂ : univ_pretopos_nat}
         (F : functor_pretopos_nat E₁ E₂)
  : functor_pretopos E₁ E₂.
Proof.
  use make_functor_pretopos.
  - exact (pr1 F).
  - exact (pr11 (pr122 F)).
  - exact (pr21 (pr122 F)).
  - exact (pr12 (pr122 F)).
Defined.

Definition functor_pretopos_nat_preserves_NNO
           {E₁ E₂ : univ_pretopos_nat}
           (F : functor_pretopos_nat E₁ E₂)
  : preserves_parameterized_NNO
      (univ_pretopos_nat_pnno E₁)
      (univ_pretopos_nat_pnno E₂)
      F
      (functor_finlim_preserves_terminal F)
  := pr222 F.

Definition make_functor_pretopos_nat
           {E₁ E₂ : univ_pretopos_nat}
           (F : functor_pretopos E₁ E₂)
           (HF : preserves_parameterized_NNO
                   (univ_pretopos_nat_pnno E₁)
                   (univ_pretopos_nat_pnno E₂)
                   F
                   (functor_finlim_preserves_terminal F))
  : functor_pretopos_nat E₁ E₂.
Proof.
  simple refine (_ ,, (tt ,, (((_ ,, _) ,, (_ ,, tt)) ,, _))).
  - exact (functor_pretopos_to_functor_finlim F).
  - exact (preserves_initial_functor_pretopos F).
  - exact (preserves_bincoproduct_functor_pretopos F).
  - exact (preserves_regular_epi_functor_pretopos F).
  - exact HF.
Defined.

Definition nat_trans_pretopos_nat
           {E₁ E₂ : univ_pretopos_nat}
           (F G : functor_pretopos_nat E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_pretopos_nat_to_nat_trans_finlim
         {E₁ E₂ : univ_pretopos_nat}
         {F G : functor_pretopos_nat E₁ E₂}
         (τ : nat_trans_pretopos_nat F G)
  : nat_trans_finlim F G
  := pr1 τ.

Definition make_nat_trans_pretopos_nat
           {E₁ E₂ : univ_pretopos_nat}
           {F G : functor_pretopos_nat E₁ E₂}
           (τ : F ⟹ G)
  : nat_trans_pretopos_nat F G
  := make_nat_trans_finlim τ ,, (tt ,, tt).

Proposition nat_trans_pretopos_nat_eq
            {E₁ E₂ : univ_pretopos_nat}
            {F G : functor_pretopos_nat E₁ E₂}
            {τ₁ τ₂ : nat_trans_pretopos_nat F G}
            (p : ∏ (x : E₁), τ₁ x = τ₂ x)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isaproptotal2.
    - intro.
      apply isapropunit.
    - intros.
      apply isapropunit.
  }
  use nat_trans_finlim_eq.
  exact p.
Qed.

(** * 3. The bicategory of pretopos comprehension categories with natural numbers *)
Definition univ_pretopos_with_nat_language
  : bicat
  := total_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat
          pretopos_with_nat_local_property).

Proposition is_univalent_2_univ_pretopos_with_nat_language
  : is_univalent_2 univ_pretopos_with_nat_language.
Proof.
  use total_is_univalent_2.
  - apply univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_univ_pretopos_with_nat_language
  : is_univalent_2_0 univ_pretopos_with_nat_language.
Proof.
  apply is_univalent_2_univ_pretopos_with_nat_language.
Qed.

Proposition is_univalent_2_1_univ_pretopos_with_nat_language
  : is_univalent_2_1 univ_pretopos_with_nat_language.
Proof.
  apply is_univalent_2_univ_pretopos_with_nat_language.
Qed.

(** * 4. Accessors for pretopos comprehension categories with natural numbers *)
Definition pretopos_comp_cat_with_nat
  : UU
  := univ_pretopos_with_nat_language.

Coercion pretopos_comp_cat_with_nat_to_dfl_comp_cat
         (C : pretopos_comp_cat_with_nat)
  : dfl_full_comp_cat
  := pr1 C.

Definition fiberwise_strict_initial_pretopos_comp_cat_with_nat
           (C : pretopos_comp_cat_with_nat)
  : fiberwise_cat_property
      strict_initial_local_property
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (pr12 C)))).

Definition fiberwise_bincoproduct_pretopos_comp_cat_with_nat
           (C : pretopos_comp_cat_with_nat)
  : fiberwise_cat_property
      stable_bincoproducts_local_property
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_sub_left
          (local_property_conj_left
             (local_property_conj_left
                (pr12 C)))).

Definition fiberwise_regular_pretopos_comp_cat_with_nat
           (C : pretopos_comp_cat_with_nat)
  : fiberwise_cat_property
      regular_local_property
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_conj_right
          (local_property_conj_left (pr12 C))).

Definition fiberwise_effective_eqrel_pretopos_comp_cat_with_nat
           (C : pretopos_comp_cat_with_nat)
  : fiberwise_cat_property
      all_eqrel_effective_local_property
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_conj_right
          (local_property_conj_left (pr12 C))).

Definition fiberwise_nno_pretopos_comp_cat_with_nat
           (C : pretopos_comp_cat_with_nat)
  : fiberwise_cat_property
      parameterized_NNO_cat_property
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C)
  := local_property_conj_right (pr12 C).

Definition pretopos_comp_cat_with_nat_functor
           (C₁ C₂ : pretopos_comp_cat_with_nat)
  : UU
  := C₁ --> C₂.

Coercion pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor
         {C₁ C₂ : pretopos_comp_cat_with_nat}
         (F : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C₁)
      (pretopos_comp_cat_with_nat_to_dfl_comp_cat C₂)
  := pr1 F.

Definition fiberwise_strict_initial_pretopos_comp_cat_with_nat_functor
           {C₁ C₂ : pretopos_comp_cat_with_nat}
           (F : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_strict_initial_pretopos_comp_cat_with_nat C₁)
      (fiberwise_strict_initial_pretopos_comp_cat_with_nat C₂)
  := local_property_functor_conj_left
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left (pr22 F)))).

Definition fiberwise_bincoproduct_pretopos_comp_cat_with_nat_functor
           {C₁ C₂ : pretopos_comp_cat_with_nat}
           (F : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_bincoproduct_pretopos_comp_cat_with_nat C₁)
      (fiberwise_bincoproduct_pretopos_comp_cat_with_nat C₂)
  := local_property_functor_conj_right
       (local_property_functor_sub_left
          (local_property_functor_conj_left
             (local_property_functor_conj_left (pr22 F)))).

Definition fiberwise_regular_pretopos_comp_cat_with_nat_functor
           {C₁ C₂ : pretopos_comp_cat_with_nat}
           (F : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_regular_pretopos_comp_cat_with_nat C₁)
      (fiberwise_regular_pretopos_comp_cat_with_nat C₂)
  := local_property_functor_conj_left
       (local_property_functor_conj_right
          (local_property_functor_conj_left (pr22 F))).

Definition fiberwise_NNO_pretopos_comp_cat_with_nat_functor
           {C₁ C₂ : pretopos_comp_cat_with_nat}
           (F : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_nno_pretopos_comp_cat_with_nat C₁)
      (fiberwise_nno_pretopos_comp_cat_with_nat C₂)
  := local_property_functor_conj_right (pr22 F).

Definition pretopos_comp_cat_with_nat_nat_trans
           {C₁ C₂ : pretopos_comp_cat_with_nat}
           (F G : pretopos_comp_cat_with_nat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion pretopos_comp_cat_with_nat_nat_trans_to_dfl_full_comp_cat_nat_trans
         {C₁ C₂ : pretopos_comp_cat_with_nat}
         {F G : pretopos_comp_cat_with_nat_functor C₁ C₂}
         (τ : pretopos_comp_cat_with_nat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor F)
      (pretopos_comp_cat_with_nat_functor_to_dfl_comp_cat_functor G)
  := pr1 τ.

(** * 5. The biequivalence *)
Definition lang_univ_pretopos_with_nat
  : psfunctor
      bicat_of_univ_pretopos_with_nat
      univ_pretopos_with_nat_language
  := total_psfunctor
       _ _ _
       (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
          pretopos_with_nat_local_property).

Definition internal_language_univ_pretopos_with_nat
  : is_biequivalence lang_univ_pretopos_with_nat
  := total_is_biequivalence
       _ _ _
       (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
          pretopos_with_nat_local_property).
