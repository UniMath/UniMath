(**

 The sheaf model of type theory

 Given a site `C` we construct a comprehension category such that
 - Contexts are sheaves over `C`
 - Types in context `Γ` are sheaves over the category of elements of `Γ`
 Since terms in comprehension categories are defined to be sections of the projection, we
 can show that terms are the same as natural families of elements in a sheaf.

 We construct this comprehension category as a full subcomprehension category of the
 presheaf model. Specifically, the sheaf model is a restriction of the presheaf model where
 we only consider contexts and types that are sheaves. Most type formers of sheaves are
 inherited from presheaves. For instance, if we have a sheaf `Γ` and sheaves `A` and `B`
 over `Γ`, then their binary product (of presheaves) is again a sheaf, which gives us an
 interpretation of binary products in the sheaf model. We can do the same for other type
 formers, like extensional identity types, ∑-types, and ∏-types. However, there are two
 type formers that require a different treatment. Both the subobject classifier type and
 the type of natural numbers of sheaves differ from their counterparts in the presheaf
 model. Hence, both these types are constructed by hand in the sheaf model.

 Content
 1. The comprehension category of sheaves as a subcomprehension category of presheaves
 2. ∏-types and the subobject classifier
 3. The category of sheaves is an elementary topos

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.PowerObject.
Require Import UniMath.CategoryTheory.ElementaryTopos.
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
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.SigmaSheaf.
Require Import UniMath.CategoryTheory.Presheaves.PiSheaf.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
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
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.PresheafModel.
Require Import UniMath.Bicategories.ComprehensionCat.SubCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

Section SheafCompCat.
  Context (C : site).

  (** * 1. The comprehension category of sheaves as a subcomprehension category of presheaves *)
  Definition is_sheaf_comp_cat_pred_data
    : comp_cat_pred_data (psh_dfl_full_comp_cat C).
  Proof.
    use make_comp_cat_pred_data.
    - intro Γ.
      use make_hProp.
      + exact (is_sheaf Γ).
      + apply isaprop_is_sheaf.
    - intros Γ HΓ A.
      use make_hProp.
      + exact (is_dep_sheaf A).
      + apply isaprop_is_dep_sheaf.
  Defined.

  Definition is_sheaf_comp_cat_pred
    : comp_cat_pred (psh_dfl_full_comp_cat C).
  Proof.
    use make_comp_cat_pred.
    - exact is_sheaf_comp_cat_pred_data.
    - apply is_sheaf_terminal.
    - exact (λ Γ A HΓ HA, is_sheaf_total_psh HΓ HA).
    - exact (λ Γ₁ Γ₂ A s HΓ₁ HΓ₂ HA, is_dep_sheaf_dep_psh_subst s HA).
  Defined.

  Definition is_sheaf_dfl_full_comp_cat_pred
    : dfl_full_comp_cat_pred (psh_dfl_full_comp_cat C).
  Proof.
    use make_dfl_full_comp_cat_pred.
    - exact is_sheaf_comp_cat_pred.
    - exact (λ Γ HΓ, is_dep_sheaf_unit_dep_psh Γ).
    - exact (λ Γ HΓ A B HA HB, is_dep_sheaf_prod_dep_psh HA HB).
    - exact (λ Γ HΓ A B τ₁ τ₂ HA HB, is_dep_sheaf_equalizer_dep_psh τ₁ τ₂ HA HB).
    - exact (λ Γ HΓ, is_dep_sheaf_psh_to_dep_psh HΓ).
    - exact (λ Γ HΓ A HA B HB, is_dep_sheaf_sigma_dep_psh HA HB).
  Defined.

  Definition sheaf_dfl_full_comp_cat
    : dfl_full_comp_cat
    := full_sub_dfl_full_comp_cat is_sheaf_dfl_full_comp_cat_pred.

  Definition sheaf_dfl_full_comp_cat_incl
    : dfl_full_comp_cat_functor
        sheaf_dfl_full_comp_cat
        (psh_dfl_full_comp_cat C)
    := full_sub_dfl_full_comp_cat_incl is_sheaf_dfl_full_comp_cat_pred.

  (** * 2. ∏-types and the subobject classifier *)
  Definition is_sheaf_dfl_full_pi_comp_cat_pred
    : dfl_full_pi_comp_cat_pred
        (psh_dfl_full_comp_cat C)
        (dependent_prod_psh_comp_cat C).
  Proof.
    use make_dfl_full_pi_comp_cat_pred.
    - exact is_sheaf_dfl_full_comp_cat_pred.
    - exact (λ Γ HΓ A HA B HB, is_dep_sheaf_pi_dep_psh A HB).
  Defined.

  Definition dependent_prod_sheaf_comp_cat
    : comp_cat_dependent_prod sheaf_dfl_full_comp_cat
    := comp_cat_dependent_prod_full_sub_dfl_full_comp_cat
         is_sheaf_dfl_full_pi_comp_cat_pred.

  Definition subobject_classifier_sheaf_comp_cat
    : fiberwise_cat_property
        subobject_classifier_local_property
        sheaf_dfl_full_comp_cat.
  Proof.
    use make_fiberwise_cat_property.
    - exact dep_sheaf_subobject_classifier.
    - intros Γ₁ Γ₂ s.
      exact (dep_sheaf_subobject_classifier_preservation s).
  Defined.

  (** * 3. The category of sheaves is an elementary topos *)
  Definition sheaf_univ_cat_with_finlim
    : univ_cat_with_finlim
    := dfl_full_comp_cat_to_finlim sheaf_dfl_full_comp_cat.

  Definition is_locally_cartesian_closed_sheaf_univ_cat_with_finlim
    : is_locally_cartesian_closed
        (pullbacks_univ_cat_with_finlim sheaf_univ_cat_with_finlim)
    := dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob
         sheaf_dfl_full_comp_cat
         dependent_prod_sheaf_comp_cat.

  Definition sheaf_univ_cat_subobject_classifier
    : subobject_classifier
        (terminal_univ_cat_with_finlim
           (dfl_full_comp_cat_to_finlim
              sheaf_dfl_full_comp_cat))
    := local_property_in_dfl_comp_cat
         subobject_classifier_local_property
         sheaf_dfl_full_comp_cat
         subobject_classifier_sheaf_comp_cat.

  Definition sheaf_topos
    : Topos.
  Proof.
    use make_Topos.
    - exact sheaf_univ_cat_with_finlim.
    - use make_Topos_Structure.
      + exact (pullbacks_univ_cat_with_finlim sheaf_univ_cat_with_finlim).
      + exact (terminal_univ_cat_with_finlim sheaf_univ_cat_with_finlim).
      + exact sheaf_univ_cat_subobject_classifier.
      + use PowerObject_from_exponentials.
        use is_locally_cartesian_closed_exponentials.
        exact is_locally_cartesian_closed_sheaf_univ_cat_with_finlim.
  Defined.
End SheafCompCat.
