(**

 The presheaf model of type theory

 One of the standard models of type theory, is the presheaf model. Specifically,
 if we have a category `C`, then we have a comprehension category as follows.
 - Contexts: presheaves over `C`
 - Morphisms between contexts: natural transformations
 - Types in context `Γ`: dependent presheaves over `Γ` (i.e., presheaves over `∫ Γ`
   where `∫ Γ` is the category of elements of `Γ`)
 - Morphisms between types: natural transformation
 - Terms are the same as sections
 We construct this model as a full comprehension category. In addition, we show that
 this model supports various type formers, like extensional identity types, a unit type,
 binary products, ∑-types, natural numbers, and ∏-types. We also show that it supports
 a subobject classifier type.

 We also show that functors and natural transformations lift to the presheaf model.

 Content
 1. The full comprehension category
 2. Type formers in the presheaf model
 3. Functors on the presheaf model
 4. Natural transformations on the presheaf model

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypesStable.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.NaturalNumbers.
Require Import UniMath.CategoryTheory.Presheaves.Precomposition.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.

Local Open Scope cat.
Local Open Scope comp_cat.

Section PShCompCat.
  Context (C : category).

  (** * 1. The full comprehension category *)
  Definition psh_cat_with_terminal_disp_cat
    : cat_with_terminal_disp_cat.
  Proof.
    use make_cat_with_terminal_disp_cat.
    - use make_univalent_category.
      + exact (PreShv C).
      + use is_univalent_functor_category.
        exact is_univalent_HSET.
    - exact Terminal_PreShv.
    - use make_disp_univalent_category.
      + exact (disp_cat_dep_psh C).
      + exact (is_univalent_disp_disp_cat_dep_psh C).
  Defined.

  Definition psh_cat_with_terminal_cleaving
    : cat_with_terminal_cleaving.
  Proof.
    use make_cat_with_terminal_cleaving.
    - exact psh_cat_with_terminal_disp_cat.
    - exact (cleaving_disp_cat_dep_psh C).
  Defined.

  Definition psh_comprehension_functor
    : comprehension_functor psh_cat_with_terminal_cleaving.
  Proof.
    use make_comprehension_functor.
    - exact (dep_psh_comprehension C).
    - exact (is_cartesian_dep_psh_comprehension C).
  Defined.

  Definition psh_comp_cat
    : comp_cat.
  Proof.
    use make_comp_cat.
    - exact psh_cat_with_terminal_cleaving.
    - exact psh_comprehension_functor.
  Defined.

  Definition psh_full_comp_cat
    : full_comp_cat.
  Proof.
    use make_full_comp_cat.
    - exact psh_comp_cat.
    - exact (disp_functor_ff_dep_psh_comprehension C).
  Defined.

  (** * 2. Type formers in the presheaf model *)
  Definition is_democratic_psh_full_comp_cat
    : is_democratic psh_full_comp_cat.
  Proof.
    intro Γ.
    exact (psh_to_dep_psh Γ ,, psh_to_dep_psh_z_iso Γ).
  Defined.

  Definition dependent_sums_psh_full_comp_cat
    : comp_cat_dependent_sum psh_full_comp_cat.
  Proof.
    use make_comp_cat_dependent_sum_from_chosen.
    use make_comp_cat_dependent_sum_chosen.
    - intros Γ A.
      exact (dependent_sum_dep_psh A).
    - intros Γ₁ Γ₂ A s B.
      use make_is_z_isomorphism.
      + exact (dep_psh_sigma_subst s A B).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx ab ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           exact (dep_psh_sigma_beck_chevalley s A B ab _)).
  Defined.

  Definition strong_dependent_sums_psh_full_comp_cat
    : strong_dependent_sums psh_full_comp_cat.
  Proof.
    refine (dependent_sums_psh_full_comp_cat ,, _).
    intros Γ A B.
    use make_is_z_isomorphism.
    - exact (dep_psh_sigma_total_inv A B).
    - abstract
        (split ;
         (use nat_trans_eq ; [ apply homset_property | ]) ;
         intro x ;
         apply idpath).
  Defined.

  Definition psh_dfl_full_comp_cat
    : dfl_full_comp_cat.
  Proof.
    use make_dfl_full_comp_cat.
    - exact psh_full_comp_cat.
    - exact is_democratic_psh_full_comp_cat.
    - exact (dep_psh_fiberwise_terminal C).
    - exact dep_psh_unit_z_iso.
    - exact (dep_psh_fiberwise_binproducts C).
    - exact (dep_psh_fiberwise_equalizers C).
    - exact strong_dependent_sums_psh_full_comp_cat.
  Defined.

  Definition dependent_prod_psh_comp_cat
    : comp_cat_dependent_prod psh_full_comp_cat.
  Proof.
    use make_comp_cat_dependent_prod_from_chosen.
    use make_comp_cat_dependent_prod_chosen.
    - intros Γ A.
      exact (dependent_product_dep_psh A).
    - intros Γ₁ Γ₂ A s B.
      use make_is_z_isomorphism.
      + exact (dep_psh_pi_subst s A B).
      + exact (dep_psh_pi_subst_inv_laws s A B _).
  Defined.

  Definition subobject_classifier_psh_comp_cat
    : fiberwise_cat_property
        subobject_classifier_local_property
        psh_dfl_full_comp_cat.
  Proof.
    use make_fiberwise_cat_property.
    - exact dep_psh_subobject_classifier.
    - intros Γ₁ Γ₂ s.
      exact (dep_psh_subobject_classifier_preservation s).
  Defined.

  Definition pnno_psh_comp_cat
    : fiberwise_cat_property
        parameterized_NNO_local_property
        psh_dfl_full_comp_cat.
  Proof.
    use make_fiberwise_cat_property.
    - intro Γ.
      refine (_ ,, _ ,, _ ,, _).
      exact (is_parameterized_NNO_prod_independent
               (C := univalent_fiber_category
                       (univalent_disp_cat_dep_psh C)
                       Γ)
               _
               (dep_psh_fiberwise_nno Γ)).
    - intros Γ₁ Γ₂ s.
      use preserves_parameterized_NNO_prod_independent.
      exact (dep_psh_fiberwise_nno_stable s).
  Defined.
End PShCompCat.

(** * 3. Functors on the presheaf model *)
Section PShCompCatFunctor.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition precomposition_psh_functor_with_terminal_disp_cat
    : functor_with_terminal_disp_cat
        (psh_dfl_full_comp_cat C₂)
        (psh_dfl_full_comp_cat C₁).
  Proof.
    use make_functor_with_terminal_disp_cat.
    - exact (precomp_psh F).
    - exact (preserves_terminal_precomp_psh F).
    - exact (precomp_dep_psh_disp_functor F).
  Defined.

  Definition precomposition_psh_functor_with_terminal_cleaving
    : functor_with_terminal_cleaving
        (psh_dfl_full_comp_cat C₂)
        (psh_dfl_full_comp_cat C₁).
  Proof.
    use make_functor_with_terminal_cleaving.
    - exact precomposition_psh_functor_with_terminal_disp_cat.
    - exact (is_cartesian_precomp_dep_psh_disp_functor F).
  Defined.

  Definition precomposition_psh_comp_cat_functor
    : comp_cat_functor
        (psh_dfl_full_comp_cat C₂)
        (psh_dfl_full_comp_cat C₁).
  Proof.
    use make_comp_cat_functor.
    - exact precomposition_psh_functor_with_terminal_cleaving.
    - exact (precomp_dep_psh_disp_functor_comprehension F).
  Defined.

  Definition precomposition_psh_full_comp_cat_functor
    : full_comp_cat_functor
        (psh_dfl_full_comp_cat C₂)
        (psh_dfl_full_comp_cat C₁).
  Proof.
    use make_full_comp_cat_functor.
    - exact precomposition_psh_comp_cat_functor.
    - exact (λ Γ A, precomp_dep_psh_disp_functor_comprehension_z_iso F A).
  Defined.

  Definition precomposition_psh_dfl_full_comp_cat_functor
    : dfl_full_comp_cat_functor
        (psh_dfl_full_comp_cat C₂)
        (psh_dfl_full_comp_cat C₁).
  Proof.
    use make_dfl_full_comp_cat_functor.
    - exact precomposition_psh_full_comp_cat_functor.
    - exact (precomp_dep_psh_disp_functor_preserves_terminal F).
    - exact (precomp_dep_psh_disp_functor_preserves_binproduct F).
    - exact (precomp_dep_psh_disp_functor_preserves_equalizer F).
  Defined.
End PShCompCatFunctor.

(** * 4. Natural transformations on the presheaf model *)
Section PShCompCatNatTrans.
  Context {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          (τ : F ⟹ G).

  Definition precomposition_psh_dfl_full_nat_trans_with_terminal_cleaving
    : nat_trans_with_terminal_cleaving
        (precomposition_psh_dfl_full_comp_cat_functor G)
        (precomposition_psh_dfl_full_comp_cat_functor F).
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - exact (precomp_psh_nat_trans τ).
    - exact (precomp_psh_disp_nat_trans τ).
  Defined.

  Definition precomposition_psh_dfl_full_comp_cat_nat_trans
    : dfl_full_comp_cat_nat_trans
        (precomposition_psh_dfl_full_comp_cat_functor G)
        (precomposition_psh_dfl_full_comp_cat_functor F).
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact precomposition_psh_dfl_full_nat_trans_with_terminal_cleaving.
    - abstract
        (intros Γ A ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         apply idpath).
  Defined.
End PShCompCatNatTrans.
