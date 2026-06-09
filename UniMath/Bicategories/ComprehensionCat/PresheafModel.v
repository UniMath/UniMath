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
 this model supports various type formers, like extensional identity, an empty type,
 unit type, binary products, binary coproducts, ∑-types, and ∏-types.

 Content
 1. The full comprehension category
 2. Type formers in the presheaf model

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.

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
End PShCompCat.
