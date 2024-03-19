(*******************************************************************************************

 The unit of the biequivalence between comprehension categories and finite limit categories

 In this file, we construct the unit of the biequivalence between comprehension categories
 and finite limit categories. We also show that the unit is a pointwise adjoint equivalence.

 Note that the construction of the unit is rather direct. If we have a category `C` with
 finite limits, it gets sent to the comprehension category whose category of contexts is
 given by `C` and whose cleaving of types is given by the codomain. This means that the
 underlying category of contexts is always definitionally equal to `C`, and the only
 difference would how the limits are constructed exactly. However, for the construction,
 this does not really matter: we can still use the identity functor.

 Contents
 1. The morphism of the unit
 2. The naturality of the unit
 3. The laws of the unit
 4. The unit
 5. The unit is a pointwise adjoint equivalence

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
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

(** * 1. The morphism of the unit *)
Definition finlim_dfl_comp_cat_unit_mor
           (C : univ_cat_with_finlim)
  : functor_finlim
      (dfl_full_comp_cat_to_finlim (finlim_to_dfl_comp_cat C))
      C.
Proof.
  use make_functor_finlim.
  - apply functor_identity.
  - apply identity_preserves_terminal.
  - apply identity_preserves_pullback.
Defined.

(** * 2. The naturality of the unit *)
Definition finlim_dfl_comp_cat_unit_natural
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
  : finlim_dfl_comp_cat_unit_mor C₁ · F
    ==>
    dfl_functor_comp_cat_to_finlim_functor
      (finlim_to_dfl_comp_cat_functor F)
    · finlim_dfl_comp_cat_unit_mor C₂.
Proof.
  use make_nat_trans_finlim.
  apply nat_trans_id.
Defined.

Definition finlim_dfl_comp_cat_unit_natural_inv2cell
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
  : invertible_2cell
      (finlim_dfl_comp_cat_unit_mor C₁ · F)
      (dfl_functor_comp_cat_to_finlim_functor
         (finlim_to_dfl_comp_cat_functor F)
       · finlim_dfl_comp_cat_unit_mor C₂).
Proof.
  use make_invertible_2cell.
  - exact (finlim_dfl_comp_cat_unit_natural F).
  - use is_invertible_2cell_cat_with_finlim.
    apply is_nat_z_iso_nat_trans_id.
Defined.

Definition finlim_dfl_comp_cat_unit_data
  : pstrans_data
      (comp_psfunctor
         dfl_comp_cat_to_finlim_psfunctor
         finlim_to_dfl_comp_cat_psfunctor)
      (id_psfunctor bicat_of_univ_cat_with_finlim).
Proof.
  use make_pstrans_data.
  - exact finlim_dfl_comp_cat_unit_mor.
  - exact (λ _ _ F, finlim_dfl_comp_cat_unit_natural_inv2cell F).
Defined.

(** * 3. The laws of the unit *)
(**
   Below, we regularly change the opacity of `comp_psfunctor` to guarantee
   that this proposition gets type checked in reasonable time.
 *)
Proposition finlim_dfl_comp_cat_unit_laws
  : is_pstrans finlim_dfl_comp_cat_unit_data.
Proof.
  refine (_ ,, _ ,, _).
  - refine (λ (C₁ C₂ : univ_cat_with_finlim)
              (F G : functor_finlim C₁ C₂)
              (τ : nat_trans_finlim F G),
            _).
    use nat_trans_finlim_eq.
    intro x ; cbn.
    rewrite id_right, id_left.
    apply idpath.
  - refine (λ (C : univ_cat_with_finlim), _).
    Opaque comp_psfunctor.
    use nat_trans_finlim_eq.
    Transparent comp_psfunctor.
    intro x ; cbn.
    rewrite !id_left.
    apply idpath.
  - refine (λ (C₁ C₂ C₃ : univ_cat_with_finlim)
              (F : functor_finlim C₁ C₂)
              (G : functor_finlim C₂ C₃),
            _).
    Opaque comp_psfunctor.
    use nat_trans_finlim_eq.
    Transparent comp_psfunctor.
    intro x ; cbn.
    rewrite !id_left, !id_right.
    exact (!(functor_id _ _)).
    Opaque comp_psfunctor.
Qed.
Transparent comp_psfunctor.

(** * 4. The unit *)
Definition finlim_dfl_comp_cat_unit
  : pstrans
      (comp_psfunctor
         dfl_comp_cat_to_finlim_psfunctor
         finlim_to_dfl_comp_cat_psfunctor)
      (id_psfunctor bicat_of_univ_cat_with_finlim).
Proof.
  use make_pstrans.
  - exact finlim_dfl_comp_cat_unit_data.
  - exact finlim_dfl_comp_cat_unit_laws.
Defined.

(** * 5. The unit is a pointwise adjoint equivalence *)
Definition finlim_dfl_comp_cat_unit_pointwise_equiv
           (C : univ_cat_with_finlim)
  : left_adjoint_equivalence (finlim_dfl_comp_cat_unit C).
Proof.
  use left_adjoint_equivalence_univ_cat_with_finlim.
  apply identity_functor_is_adj_equivalence.
Defined.

Definition finlim_dfl_comp_cat_unit_left_adjoint_equivalence
  : left_adjoint_equivalence finlim_dfl_comp_cat_unit.
Proof.
  use pointwise_adjequiv_to_adjequiv.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - exact finlim_dfl_comp_cat_unit_pointwise_equiv.
Defined.

Definition finlim_dfl_comp_cat_unit_inv
  : pstrans
      (id_psfunctor bicat_of_univ_cat_with_finlim)
      (comp_psfunctor
         dfl_comp_cat_to_finlim_psfunctor
         finlim_to_dfl_comp_cat_psfunctor)
  := left_adjoint_right_adjoint
       finlim_dfl_comp_cat_unit_left_adjoint_equivalence.

Proposition finlim_dfl_comp_cat_unit_inv_pointwise
            (C : univ_cat_with_finlim)
  : finlim_dfl_comp_cat_unit_inv C
    =
    left_adjoint_right_adjoint (finlim_dfl_comp_cat_unit_pointwise_equiv C).
Proof.
  apply right_adjoint_pointwise_adjequiv.
Qed.
