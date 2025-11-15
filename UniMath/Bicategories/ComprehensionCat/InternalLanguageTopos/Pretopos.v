(**

 The internal language of pretoposes

 In other files, we gave several extensions of the biequivalence between categories with
 finite limits and full DFL comprehension categories. Now we put these extensions together
 in order to obtain internal language theorems for several classes of toposes. The results
 are split over several files.

 In this file, we consider pretoposes. A pretopos is a category that is extensive and exact.
 This can be expressed via a local property (i.e., a property on categories that is closed
 under slicing, see the file `LocalProperty.LocalProperties.v`), and from that we directly
 obtain the biequivalence. The internal language of this class of toposes is given by
 extensional type theory with ∑-types, quotient types, and disjoint sum types.

 Contents
 1. The bicategory of pretoposes
 2. Accessors for pretoposes
 3. The bicategory of pretopos comprehension categories
 4. Accessors for pretopos comprehension categories
 5. The biequivalence

                                                                                          *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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

Local Open Scope cat.

(** * 1. The bicategory of pretoposes *)
Definition bicat_of_univ_pretopos
  : bicat
  := total_bicat
       (disp_bicat_of_univ_cat_with_cat_property pretopos_local_property).

Proposition is_univalent_2_bicat_of_univ_pretopos
  : is_univalent_2 bicat_of_univ_pretopos.
Proof.
  use total_is_univalent_2.
  - apply disp_univalent_2_disp_bicat_univ_cat_with_cat_property.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_0_bicat_of_univ_pretopos
  : is_univalent_2_0 bicat_of_univ_pretopos.
Proof.
  apply is_univalent_2_bicat_of_univ_pretopos.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_pretopos
  : is_univalent_2_1 bicat_of_univ_pretopos.
Proof.
  apply is_univalent_2_bicat_of_univ_pretopos.
Qed.

(** * 2. Accessors for pretoposes *)
Definition univ_pretopos
  : UU
  := bicat_of_univ_pretopos.

Coercion pretopos_to_finlim
         (E : univ_pretopos)
  : univ_cat_with_finlim
  := pr1 E.

Definition strict_initial_univ_pretopos
           (E : univ_pretopos)
  : strict_initial_object E
  := pr11 (pr112 E).

Definition bincoproducts_univ_pretopos
           (E : univ_pretopos)
  : BinCoproducts E
  := pr121 (pr112 E).

Definition stable_bincoproducts_univ_pretopos
           (E : univ_pretopos)
  : stable_bincoproducts (bincoproducts_univ_pretopos E)
  := pr221 (pr112 E).

Definition disjoint_bincoproducts_univ_pretopos
           (E : univ_pretopos)
  : disjoint_bincoproducts
      (bincoproducts_univ_pretopos E)
      (strict_initial_univ_pretopos E)
  := pr2 (pr112 E).

Definition is_regular_category_univ_pretopos
           (E : univ_pretopos)
  : is_regular_category E.
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (terminal_univ_cat_with_finlim E).
  - exact (pullbacks_univ_cat_with_finlim E).
  - exact (pr1 (pr121 (pr2 E))).
  - exact (pr2 (pr121 (pr2 E))).
Defined.

Definition all_internal_eqrel_effective_univ_pretopos
           (E : univ_pretopos)
  : all_internal_eqrel_effective E
  := pr221 (pr2 E).

Definition make_univ_pretopos
           {C : univ_cat_with_finlim}
           (I : strict_initial_object C)
           (BC : BinCoproducts C)
           (HBC₁ : stable_bincoproducts BC)
           (HBC₂ : disjoint_bincoproducts BC I)
           (coeq : coeqs_of_kernel_pair C)
           (stable : regular_epi_pb_stable C)
           (exa : all_internal_eqrel_effective C)
  : univ_pretopos.
Proof.
  simple refine (C ,, (((_ ,, (_ ,, _)) ,, _) ,, (_ ,, _) ,, _) ,, tt).
  - exact I.
  - exact BC.
  - exact HBC₁.
  - exact HBC₂.
  - exact coeq.
  - exact stable.
  - exact exa.
Defined.

Definition functor_pretopos
           (E₁ E₂ : univ_pretopos)
  : UU
  := E₁ --> E₂.

Coercion functor_pretopos_to_functor_finlim
         {E₁ E₂ : univ_pretopos}
         (F : functor_pretopos E₁ E₂)
  : functor_finlim E₁ E₂
  := pr1 F.

Definition preserves_initial_functor_pretopos
           {E₁ E₂ : univ_pretopos}
           (F : functor_pretopos E₁ E₂)
  : preserves_initial F
  := pr1 (pr122 F).

Definition preserves_bincoproduct_functor_pretopos
           {E₁ E₂ : univ_pretopos}
           (F : functor_pretopos E₁ E₂)
  : preserves_bincoproduct F
  := pr2 (pr122 F).

Definition preserves_regular_epi_functor_pretopos
           {E₁ E₂ : univ_pretopos}
           (F : functor_pretopos E₁ E₂)
  : preserves_regular_epi F
  := pr1 (pr222 F).

Definition make_functor_pretopos
           {E₁ E₂ : univ_pretopos}
           (F : functor_finlim E₁ E₂)
           (HF₁ : preserves_initial F)
           (HF₂ : preserves_bincoproduct F)
           (HF₃ : preserves_regular_epi F)
  : functor_pretopos E₁ E₂
  := F ,, tt ,, (HF₁ ,, HF₂) ,, (HF₃ ,, tt).

Definition nat_trans_pretopos
           {E₁ E₂ : univ_pretopos}
           (F G : functor_pretopos E₁ E₂)
  : UU
  := F ==> G.

Coercion nat_trans_pretopos_to_nat_trans_finlim
         {E₁ E₂ : univ_pretopos}
         {F G : functor_pretopos E₁ E₂}
         (τ : nat_trans_pretopos F G)
  : nat_trans_finlim F G
  := pr1 τ.

Definition make_nat_trans_pretopos
           {E₁ E₂ : univ_pretopos}
           {F G : functor_pretopos E₁ E₂}
           (τ : F ⟹ G)
  : nat_trans_pretopos F G
  := make_nat_trans_finlim τ ,, (tt ,, tt).

Proposition nat_trans_pretopos_eq
            {E₁ E₂ : univ_pretopos}
            {F G : functor_pretopos E₁ E₂}
            {τ₁ τ₂ : nat_trans_pretopos F G}
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

(** * 3. The bicategory of pretopos comprehension categories *)
Definition univ_pretopos_language
  : bicat
  := total_bicat
       (disp_bicat_of_cat_property_dfl_full_comp_cat pretopos_local_property).

Proposition is_univalent_2_univ_pretopos_language
  : is_univalent_2 univ_pretopos_language.
Proof.
  use total_is_univalent_2.
  - apply univalent_2_disp_bicat_of_cat_property_dfl_full_comp_cat.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_univ_pretopos_language
  : is_univalent_2_0 univ_pretopos_language.
Proof.
  apply is_univalent_2_univ_pretopos_language.
Qed.

Proposition is_univalent_2_1_univ_pretopos_language
  : is_univalent_2_1 univ_pretopos_language.
Proof.
  apply is_univalent_2_univ_pretopos_language.
Qed.

(** * 4. Accessors for pretopos comprehension categories *)
Definition pretopos_comp_cat
  : UU
  := univ_pretopos_language.

Coercion pretopos_comp_cat_to_dfl_comp_cat
         (C : pretopos_comp_cat)
  : dfl_full_comp_cat
  := pr1 C.

Definition fiberwise_strict_initial_pretopos_comp_cat
           (C : pretopos_comp_cat)
  : fiberwise_cat_property
      strict_initial_local_property
      (pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left
       (local_property_sub_left
          (local_property_conj_left
             (pr12 C))).

Definition fiberwise_bincoproduct_pretopos_comp_cat
           (C : pretopos_comp_cat)
  : fiberwise_cat_property
      stable_bincoproducts_local_property
      (pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right
       (local_property_sub_left
          (local_property_conj_left
             (pr12 C))).

Definition fiberwise_regular_pretopos_comp_cat
           (C : pretopos_comp_cat)
  : fiberwise_cat_property
      regular_local_property
      (pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_left (local_property_conj_right (pr12 C)).

Definition fiberwise_effective_eqrel_pretopos_comp_cat
           (C : pretopos_comp_cat)
  : fiberwise_cat_property
      all_eqrel_effective_local_property
      (pretopos_comp_cat_to_dfl_comp_cat C)
  := local_property_conj_right (local_property_conj_right (pr12 C)).

Definition pretopos_comp_cat_functor
           (C₁ C₂ : pretopos_comp_cat)
  : UU
  := C₁ --> C₂.

Coercion pretopos_comp_cat_functor_to_dfl_comp_cat_functor
         {C₁ C₂ : pretopos_comp_cat}
         (F : pretopos_comp_cat_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (pretopos_comp_cat_to_dfl_comp_cat C₁)
      (pretopos_comp_cat_to_dfl_comp_cat C₂)
  := pr1 F.

Definition fiberwise_strict_initial_pretopos_comp_cat_functor
           {C₁ C₂ : pretopos_comp_cat}
           (F : pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_strict_initial_pretopos_comp_cat C₁)
      (fiberwise_strict_initial_pretopos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_sub_left
          (local_property_functor_conj_left (pr22 F))).

Definition fiberwise_bincoproduct_pretopos_comp_cat_functor
           {C₁ C₂ : pretopos_comp_cat}
           (F : pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_bincoproduct_pretopos_comp_cat C₁)
      (fiberwise_bincoproduct_pretopos_comp_cat C₂)
  := local_property_functor_conj_right
       (local_property_functor_sub_left
          (local_property_functor_conj_left (pr22 F))).

Definition fiberwise_regular_pretopos_comp_cat_functor
           {C₁ C₂ : pretopos_comp_cat}
           (F : pretopos_comp_cat_functor C₁ C₂)
  : fiberwise_cat_property_functor
      (pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (fiberwise_regular_pretopos_comp_cat C₁)
      (fiberwise_regular_pretopos_comp_cat C₂)
  := local_property_functor_conj_left
       (local_property_functor_conj_right (pr22 F)).

Definition pretopos_comp_cat_nat_trans
           {C₁ C₂ : pretopos_comp_cat}
           (F G : pretopos_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion pretopos_comp_cat_nat_trans_to_dfl_full_comp_cat_nat_trans
         {C₁ C₂ : pretopos_comp_cat}
         {F G : pretopos_comp_cat_functor C₁ C₂}
         (τ : pretopos_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans
      (pretopos_comp_cat_functor_to_dfl_comp_cat_functor F)
      (pretopos_comp_cat_functor_to_dfl_comp_cat_functor G)
  := pr1 τ.

(** * 5. The biequivalence *)
Definition lang_univ_pretopos
  : psfunctor
      bicat_of_univ_pretopos
      univ_pretopos_language
  := total_psfunctor
       _ _ _
       (finlim_biequiv_dfl_comp_cat_disp_psfunctor_local_property
          pretopos_local_property).

Definition internal_language_univ_pretopos
  : is_biequivalence lang_univ_pretopos
  := total_is_biequivalence
       _ _ _
       (finlim_biequiv_dfl_comp_cat_psfunctor_local_property
          pretopos_local_property).
