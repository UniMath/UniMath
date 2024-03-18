(*******************************************************************************************

 The counit of the biequivalence between comprehension categories and finite limit categories

 In this file, we construct the counit of the biequivalence between comprehension categories
 and finite limit categories. We also show that the counit is an adjoint equivalence.

 Suppose that we have a full DFL comprehension category `C`. The counit of the biequivalence
 is given by a family of functors going from the category of types in `C` to the codomain
 fibration on the category of contexts of `C`. This is given by the comprehension functor
 in `C`.

 The crucial observation behind this construction is that the comprehension functor is an
 equivalence. Since we assume the comprehension categories are full, the comprehension
 functor is always faithful. It thus suffices to show that the comprehension functor is
 essentially surjective. This is the essence behind the proof of Proposition 2.9 in the
 paper "The biequivalence of locally cartesian closed categories and Martin-Löf type theories"
 by Clairambault and Dybjer, and it is where sigma types, identity types, and democracy are
 used.

 References
 - "The biequivalence of locally cartesian closed categories and Martin-Löf type theories" by
   Clairambault and Dybjer

 Contents
 1. The morphism of the counit
 2. The naturality of the counit
 3. The data of the counit
 4. The laws of the counit
 5. The counit
 6. The counit is an adjoint equivalence

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
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.

(** * 1. The morphism of the counit *)
Section FinLimDFLCompCatCounit.
  Context (C : dfl_full_comp_cat).

  Definition finlim_dfl_comp_cat_counit_mor_terminal_disp_cat
    : functor_with_terminal_disp_cat
        C
        (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C)).
  Proof.
    use make_functor_with_terminal_disp_cat.
    - apply functor_identity.
    - apply identity_preserves_terminal.
    - exact (comp_cat_comprehension C).
  Defined.

  Definition finlim_dfl_comp_cat_counit_mor_terminal_cleaving
    : functor_with_terminal_cleaving
        C
        (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C)).
  Proof.
    use make_functor_with_terminal_cleaving.
    - exact finlim_dfl_comp_cat_counit_mor_terminal_disp_cat.
    - exact (pr2 (comp_cat_comprehension C)).
  Defined.

  Definition finlim_dfl_comp_cat_counit_mor_nat_trans
    : comprehension_nat_trans
        (comp_cat_comprehension C)
        (comp_cat_comprehension
           (finlim_to_dfl_comp_cat
              (dfl_full_comp_cat_to_finlim C)))
        finlim_dfl_comp_cat_counit_mor_terminal_cleaving.
  Proof.
    simple refine (_ ,, _).
    - refine (λ x xx, identity _ ,, _).
      abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (intros x y f xx yy ff ;
         use eq_cod_mor ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition finlim_dfl_comp_cat_counit_mor_comp_cat
    : comp_cat_functor
        C
        (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C)).
  Proof.
    use make_comp_cat_functor.
    - exact finlim_dfl_comp_cat_counit_mor_terminal_cleaving.
    - exact finlim_dfl_comp_cat_counit_mor_nat_trans.
  Defined.

  Definition finlim_dfl_comp_cat_counit_mor_full_comp_cat
    : full_comp_cat_functor
        C
        (finlim_to_dfl_comp_cat
           (dfl_full_comp_cat_to_finlim C)).
  Proof.
    use make_full_comp_cat_functor.
    - exact finlim_dfl_comp_cat_counit_mor_comp_cat.
    - intros x xx.
      apply is_z_isomorphism_identity.
  Defined.

  Definition finlim_dfl_comp_cat_counit_mor
    : dfl_full_comp_cat_functor
        C
        (finlim_to_dfl_comp_cat
           (dfl_full_comp_cat_to_finlim C)).
  Proof.
    use make_dfl_full_comp_cat_functor.
    - exact finlim_dfl_comp_cat_counit_mor_full_comp_cat.
    - exact (preserves_terminal_fiber_functor_comprehension C).
    - exact (preserves_binproduct_fiber_functor_comprehension C).
    - exact (preserves_equalizer_fiber_functor_comprehension C).
  Defined.
End FinLimDFLCompCatCounit.

(** * 2. The naturality of the counit *)
Section FinLimDFLCompCatCounitNatural.
  Context {C₁ C₂ : dfl_full_comp_cat}
          (F : dfl_full_comp_cat_functor C₁ C₂).

  Let ε₁ : dfl_full_comp_cat_functor
             C₁
             (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₁))
    := finlim_dfl_comp_cat_counit_mor C₁.

  Let ε₂ : dfl_full_comp_cat_functor
             C₂
             (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₂))
    := finlim_dfl_comp_cat_counit_mor C₂.

  Let F'
    : dfl_full_comp_cat_functor
        (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₁))
        (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₂))
    := finlim_to_dfl_comp_cat_functor
         (dfl_functor_comp_cat_to_finlim_functor F).

  Let G₁ : dfl_full_comp_cat_functor
             C₁
             (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₂))
      := ε₁ · F'.
  Let G₂ : dfl_full_comp_cat_functor
             C₁
             (finlim_to_dfl_comp_cat (dfl_full_comp_cat_to_finlim C₂))
    := F · ε₂.

  Definition finlim_dfl_comp_cat_counit_natural_terminal_cleaving
    : nat_trans_with_terminal_cleaving G₁ G₂.
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - apply nat_trans_id.
    - exact (comp_cat_functor_comprehension F).
  Defined.

  Proposition finlim_dfl_comp_cat_counit_natural_eq
    : comprehension_nat_trans_eq
        finlim_dfl_comp_cat_counit_natural_terminal_cleaving
        (comp_cat_functor_comprehension G₁)
        (comp_cat_functor_comprehension G₂).
  Proof.
    intros x xx.
    cbn.
    rewrite !functor_id, !id_left, !id_right.
    apply idpath.
  Qed.

  Definition finlim_dfl_comp_cat_counit_natural
    : dfl_full_comp_cat_nat_trans G₁ G₂.
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact finlim_dfl_comp_cat_counit_natural_terminal_cleaving.
    - exact finlim_dfl_comp_cat_counit_natural_eq.
  Defined.

  Definition is_invertible_2cell_finlim_dfl_comp_cat_counit_natural
    : is_invertible_2cell finlim_dfl_comp_cat_counit_natural.
  Proof.
    use is_invertible_dfl_full_comp_cat_nat_trans.
    - intro x.
      apply is_z_isomorphism_identity.
    - intros x xx.
      use is_z_iso_disp_codomain'.
      exact (full_comp_cat_functor_is_z_iso F xx).
  Defined.

  Definition finlim_dfl_comp_cat_counit_natural_inv2cell
    : invertible_2cell G₁ G₂.
  Proof.
    use make_invertible_2cell.
    - exact finlim_dfl_comp_cat_counit_natural.
    - exact is_invertible_2cell_finlim_dfl_comp_cat_counit_natural.
  Defined.
End FinLimDFLCompCatCounitNatural.

(** * 3. The data of the counit *)
Definition finlim_dfl_comp_cat_counit_data
  : pstrans_data
      (id_psfunctor bicat_of_dfl_full_comp_cat)
      (comp_psfunctor
         finlim_to_dfl_comp_cat_psfunctor
         dfl_comp_cat_to_finlim_psfunctor).
Proof.
  use make_pstrans_data.
  - exact (λ C, finlim_dfl_comp_cat_counit_mor C).
  - exact (λ _ _ F, finlim_dfl_comp_cat_counit_natural_inv2cell F).
Defined.

(** * 4. The laws of the counit *)
Proposition finlim_dfl_comp_cat_counit_laws
  : is_pstrans finlim_dfl_comp_cat_counit_data.
Proof.
  refine (_ ,, _ ,, _).
  - refine (λ (C₁ C₂ : dfl_full_comp_cat)
              (F G : dfl_full_comp_cat_functor C₁ C₂)
              (τ : dfl_full_comp_cat_nat_trans F G),
            _).
    use dfl_full_comp_cat_nat_trans_eq.
    + abstract
        (intro x ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      exact (!(comp_cat_nat_trans_comprehension τ xx)).
  - refine (λ (C : dfl_full_comp_cat), _).
    use dfl_full_comp_cat_nat_trans_eq.
    + intro x ; cbn.
      apply idpath.
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_left.
      refine (!_).
      exact (comprehension_functor_mor_id (comp_cat_comprehension C) xx).
  - refine (λ (C₁ C₂ C₃ : dfl_full_comp_cat)
              (F : dfl_full_comp_cat_functor C₁ C₂)
              (G : dfl_full_comp_cat_functor C₂ C₃),
            _).
    use dfl_full_comp_cat_nat_trans_eq.
    + intro x ; cbn.
      rewrite !id_left, !id_right.
      exact (!(functor_id _ _)).
    + intros x xx.
      use eq_cod_mor.
      rewrite transportf_cod_disp.
      cbn.
      rewrite !id_left, !id_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (comprehension_functor_mor_id (comp_cat_comprehension C₃)).
      }
      apply id_right.
Qed.

(** * 5. The counit *)
Definition finlim_dfl_comp_cat_counit
  : pstrans
      (id_psfunctor bicat_of_dfl_full_comp_cat)
      (comp_psfunctor
         finlim_to_dfl_comp_cat_psfunctor
         dfl_comp_cat_to_finlim_psfunctor).
Proof.
  use make_pstrans.
  - exact finlim_dfl_comp_cat_counit_data.
  - exact finlim_dfl_comp_cat_counit_laws.
Defined.

(** * 6. The counit is an adjoint equivalence *)
Definition finlim_dfl_comp_cat_counit_pointwise_equiv
           (C : dfl_full_comp_cat)
  : left_adjoint_equivalence (finlim_dfl_comp_cat_counit C).
Proof.
  use dfl_full_comp_cat_left_adjoint_equivalence.
  - exact identity_functor_is_adj_equivalence.
  - use is_equiv_over_id_to_is_equiv_over.
    exact (is_equiv_over_id_comprehension C).
Defined.

Definition finlim_dfl_comp_cat_counit_left_adjoint_equivalence
  : left_adjoint_equivalence finlim_dfl_comp_cat_counit.
Proof.
  use pointwise_adjequiv_to_adjequiv.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
  - exact finlim_dfl_comp_cat_counit_pointwise_equiv.
Defined.

Definition finlim_dfl_comp_cat_counit_inv
  : pstrans
      (comp_psfunctor
         finlim_to_dfl_comp_cat_psfunctor
         dfl_comp_cat_to_finlim_psfunctor)
      (id_psfunctor bicat_of_dfl_full_comp_cat)
  := left_adjoint_right_adjoint
       finlim_dfl_comp_cat_counit_left_adjoint_equivalence.

Proposition finlim_dfl_comp_cat_counit_inv_pointwise
            (C : bicat_of_dfl_full_comp_cat)
  : finlim_dfl_comp_cat_counit_inv C
    =
    left_adjoint_right_adjoint (finlim_dfl_comp_cat_counit_pointwise_equiv C).
Proof.
  apply right_adjoint_pointwise_adjequiv.
Qed.
