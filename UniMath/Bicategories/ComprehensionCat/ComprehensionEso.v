(*******************************************************************************************

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FullyFaithfulDispFunctor.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.

Definition TODO { A : UU } : A.
Admitted.

Section ComprehensionEso.
  Context (C : dfl_full_comp_cat).

  Definition comprehension_eso
    : disp_functor_disp_ess_split_surj (comp_cat_comprehension C).
  Proof.
    intros Γ Δ.
  Admitted.

  Definition is_equiv_over_id_comprehension
    : is_equiv_over_id (comp_cat_comprehension C).
  Proof.
    use is_equiv_from_ff_ess_over_id.
    - exact comprehension_eso.
    - exact (full_comp_cat_comprehension_fully_faithful C).
  Defined.

  Definition fiber_functor_comprehension_adj_equiv
             (Γ : C)
    : adj_equivalence_of_cats
        (fiber_functor (comp_cat_comprehension C) Γ)
    := fiber_equiv is_equiv_over_id_comprehension Γ.

  Definition preserves_terminal_fiber_functor_comprehension
             (Γ : C)
    : preserves_terminal (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_terminal
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).

  Definition preserves_binproduct_fiber_functor_comprehension
             (Γ : C)
    : preserves_binproduct (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_binproduct
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).

  Definition preserves_equalizer_fiber_functor_comprehension
             (Γ : C)
    : preserves_equalizer (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_equalizer
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).
End ComprehensionEso.
