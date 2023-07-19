(*************************************************************************

 Indexed transformations give rise to displayed transformations

 We show that every indexed transformation between indexed functors give
 rise to a displayed natural transformation between their corresponding
 cartesian functors.

 Contents
 1. The data
 2. The proof of naturality
 3. The displayed natural transformation

 *************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformation.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategoryToFibration.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctorToCartesian.

Local Open Scope cat.

Section IndexedTransformationToDispNatTrans.
  Context {C : category}
          {Φ Ψ : indexed_cat (C^opp)}
          {τ θ: indexed_functor Φ Ψ}
          (m : indexed_nat_trans τ θ).

  (**
   1. The data
   *)
  Definition indexed_nat_trans_to_disp_nat_trans_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (indexed_functor_to_cartesian_disp_functor τ)
        (indexed_functor_to_cartesian_disp_functor θ)
    := λ x xx, m x xx · indexed_cat_id Ψ _ (θ x xx).

  (**
   2. The proof of naturality
   *)
  Proposition indexed_nat_trans_to_disp_nat_trans_axioms
    : disp_nat_trans_axioms indexed_nat_trans_to_disp_nat_trans_data.
  Proof.
    intros x y f xx yy ff ; cbn in *.
    unfold transportb, indexed_nat_trans_to_disp_nat_trans_data.
    rewrite !functor_comp.
    refine (_ @ !(transportf_indexed_cat_to_disp_cat _ _ _)).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      exact (!(indexed_nat_trans_natural_inv m f yy)).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply (nat_trans_ax (m x)).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax (indexed_cat_id Ψ x)).
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax (indexed_cat_id Ψ x)).
    }
    cbn.
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (_ @ !(indexed_cat_lunitor_alt Ψ _ _)).
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (indexed_cat_runitor_alt Ψ).
    }
    refine (!(pr1_idtoiso_concat _ _) @ _).
    do 2 apply maponpaths.
    refine (!(maponpathscomp0 (λ g, (Ψ $ g) (θ y yy)) _ _) @ _).
    apply maponpaths.
    apply homset_property.
  Qed.

  (**
   3. The displayed natural transformation
   *)
  Definition indexed_nat_trans_to_disp_nat_trans
    : disp_nat_trans
        (nat_trans_id _)
        (indexed_functor_to_cartesian_disp_functor τ)
        (indexed_functor_to_cartesian_disp_functor θ).
  Proof.
    simple refine (_ ,, _).
    - exact indexed_nat_trans_to_disp_nat_trans_data.
    - exact indexed_nat_trans_to_disp_nat_trans_axioms.
  Defined.
End IndexedTransformationToDispNatTrans.

Arguments indexed_nat_trans_to_disp_nat_trans_data {C Φ Ψ τ θ} m /.
