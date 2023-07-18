(************************************************************************

 Grothendieck construction: the unit

 The Grothendieck construction gives a biequivalence between the
 bicategory of fibrations over a fixed category `C` and the bicategory
 of indexed categories over `C`. To construct this biequivalence, we
 need to construct the following:
 1. A pseudofunctor from the bicategory of fibrations to the bicategory
    of pseudofunctors
 2. A pseudofunctor from the bicategory of pseudofunctors to the
    bicategory of fibrations
 3. The unit and a proof that it is a pointwise adjoint equivalence
 4. The counit and a proof that it is a pointwise adjoint equivalence

 In this file, we construct the third part of this biequivalence, namely
 the unit.

 Contents
 1. Action on objects
 2. Action on 1-cells
 3. The data
 4. The laws
 5. The unit
 6. The action on objects forms an equivalence
 7. The unit is a pointwise adjoint equivalence

 ************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformation.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.CartesianToIndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.NatTransToIndexed.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategoryToFibration.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctorToCartesian.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedTransformationToTransformation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.Core.Examples.FibSlice.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PseudoFunctorsIntoCat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.PseudoTransformationIntoCat.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.ModificationIntoCat.
Require Import UniMath.Bicategories.Grothendieck.FibrationToPseudoFunctor.
Require Import UniMath.Bicategories.Grothendieck.PseudoFunctorToFibration.

Local Open Scope cat.

Section GrothendieckConstruction.
  Context {C : univalent_category}.

  Local Notation "'tr' P x" := (transportf P _ x) (at level 100, only printing).

  (**
   1. Action on objects
   *)
  Definition psfunctor_fib_to_psfunctor_unit_disp_functor_data
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_functor_data
        (functor_identity C)
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD))))
        D.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, xx).
    - cbn.
      refine (λ x y xx yy f ff,
             transportf
               (λ z, _ -->[ z ] _)
               _
               (ff ;; HD y x f yy)%mor_disp).
      abstract (apply id_left).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_unit_disp_functor_axioms
              (D : disp_univalent_category C)
              (HD : cleaving D)
    : disp_functor_axioms
        (psfunctor_fib_to_psfunctor_unit_disp_functor_data D HD).
  Proof.
    split.
    - intros x xx ; cbn.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intros x y z xx yy zz f g ff gg ; cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !assoc_disp_var.
      rewrite !transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        apply idpath.
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_disp_functor
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_functor
        (functor_identity C)
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD))))
        D.
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor_data D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor_axioms D HD).
  Defined.

  Opaque psfunctor_to_indexed_cat.

  Definition is_cartesian_psfunctor_fib_to_psfunctor_unit_disp_functor
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : is_cartesian_disp_functor
        (psfunctor_fib_to_psfunctor_unit_disp_functor D HD).
  Proof.
    intros x y f xx yy ff Hff.
    use is_cartesian_transportf.
    use is_cartesian_comp_disp.
    - use is_cartesian_z_iso_disp.
      + exact (pr2 (identity_z_iso y)).
      + refine (z_iso_disp_from_z_iso_fiber D y yy (pr1 (HD x y f xx)) (ff ,, _)).
        cbn in xx, yy, ff.
        exact (is_cartesian_to_iso_indexed_cat
                 (psfunctor_to_indexed_cat
                    (indexed_cat_to_psfunctor
                       (cleaving_to_indexed_cat D HD)))
                  ff
                  Hff).
    - apply cartesian_lift_is_cartesian.
  Qed.

  Transparent psfunctor_to_indexed_cat.

  Definition psfunctor_fib_to_psfunctor_unit_cartesian_disp_functor
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : cartesian_disp_functor
        (functor_identity C)
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD))))
        D.
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor D HD).
    - exact (is_cartesian_psfunctor_fib_to_psfunctor_unit_disp_functor D HD).
  Defined.

  (**
   2. Action on 1-cells
   *)
  Definition psfunctor_fib_to_psfunctor_unit_natural_data
             {D₁ D₂ : disp_univalent_category C}
             (HD₁ : cleaving D₁)
             (HD₂ : cleaving D₂)
             (F : cartesian_disp_functor (functor_identity _) D₁ D₂)
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor D₁ HD₁)
           F)
        (disp_functor_over_id_composite
           (indexed_functor_to_disp_functor
              (pstrans_to_indexed_functor
                 (indexed_functor_to_pstrans
                    (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F))))
           (psfunctor_fib_to_psfunctor_unit_disp_functor D₂ HD₂))
    := λ x xx, id_disp _.

  Proposition psfunctor_fib_to_psfunctor_unit_natural_axioms
              {D₁ D₂ : disp_univalent_category C}
              (HD₁ : cleaving D₁)
              (HD₂ : cleaving D₂)
              (F : cartesian_disp_functor (functor_identity _) D₁ D₂)
    : disp_nat_trans_axioms
        (psfunctor_fib_to_psfunctor_unit_natural_data HD₁ HD₂ F).
  Proof.
    intros x y f xx yy ff ; cbn.
    unfold transportb, fiber_functor_natural_inv, psfunctor_fib_to_psfunctor_unit_natural_data.
    rewrite (disp_functor_transportf _ F).
    rewrite mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite id_right_disp.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_natural
             {D₁ D₂ : disp_univalent_category C}
             (HD₁ : cleaving D₁)
             (HD₂ : cleaving D₂)
             (F : cartesian_disp_functor (functor_identity _) D₁ D₂)
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor D₁ HD₁)
           F)
        (disp_functor_over_id_composite
           (indexed_functor_to_disp_functor
              (pstrans_to_indexed_functor
                 (indexed_functor_to_pstrans
                    (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F))))
           (psfunctor_fib_to_psfunctor_unit_disp_functor D₂ HD₂)).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_natural_data HD₁ HD₂ F).
    - exact (psfunctor_fib_to_psfunctor_unit_natural_axioms HD₁ HD₂ F).
  Defined.

  (**
   3. The data
   *)
  Definition psfunctor_fib_to_psfunctor_unit_data
    : pstrans_data
        (comp_psfunctor
           (psfunctor_psfunctor_bicat_to_fib C)
           (psfunctor_fib_to_psfunctor_bicat C))
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - exact (λ P, psfunctor_fib_to_psfunctor_unit_cartesian_disp_functor
                    (pr1 P) (pr2 P)).
    - simple refine (λ P₁ P₂ F, make_invertible_2cell _).
      + exact (psfunctor_fib_to_psfunctor_unit_natural (pr2 P₁) (pr2 P₂) F).
      + use is_invertible_2cell_fib_slice.
        intros x xx.
        apply id_is_z_iso_disp.
  Defined.

  (**
   4. The laws
   *)
  Proposition is_pstrans_psfunctor_fib_to_psfunctor_unit
    : is_pstrans psfunctor_fib_to_psfunctor_unit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros P₁ P₂ F G τ.
      use disp_nat_trans_eq.
      intros x xx.
      cbn ; unfold psfunctor_fib_to_psfunctor_unit_natural_data.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite id_right_disp.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros P.
      use disp_nat_trans_eq.
      intros x xx.
      cbn ; unfold psfunctor_fib_to_psfunctor_unit_natural_data.
      rewrite transportf_object_cartesian_lift.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite !transport_f_f.
      rewrite assoc_disp_var.
      rewrite !transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        unfold transportb.
        rewrite cartesian_factorisation_commutes.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite assoc_disp_var.
        rewrite cartesian_factorisation_commutes.
        rewrite transport_f_f.
        apply idpath.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros P₁ P₂ P₃ F G.
      use disp_nat_trans_eq.
      intros x xx.
      cbn ; unfold psfunctor_fib_to_psfunctor_unit_natural_data.
      rewrite transportf_object_cartesian_lift.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite (disp_functor_id (pr1 G)).
      rewrite !id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        unfold transportb.
        rewrite cartesian_factorisation_commutes.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite assoc_disp_var.
        rewrite transport_f_f.
        rewrite cartesian_factorisation_commutes.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite id_right_disp.
        unfold transportb.
        rewrite transport_f_f.
        apply idpath.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
      Opaque comp_psfunctor.
  Qed.
  Transparent comp_psfunctor.

  (**
   5. The unit
   *)
  Definition psfunctor_fib_to_psfunctor_unit
    : pstrans
        (comp_psfunctor
           (psfunctor_psfunctor_bicat_to_fib C)
           (psfunctor_fib_to_psfunctor_bicat C))
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact psfunctor_fib_to_psfunctor_unit_data.
    - exact is_pstrans_psfunctor_fib_to_psfunctor_unit.
  Defined.

  (**
   6. The action on objects forms an equivalence
   *)
  Definition psfunctor_fib_to_psfunctor_unit_disp_functor_inv_data
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_functor_data
        (functor_identity C)
        D
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD)))).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, xx).
    - cbn.
      refine (λ x y xx yy f ff,
              cartesian_factorisation
                (HD y x f yy)
                _
                (transportf
                   (λ z, _ -->[ z ] _)
                   _
                   ff)).
      abstract
        (exact (!(id_left _))).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_unit_disp_functor_inv_axioms
              (D : disp_univalent_category C)
              (HD : cleaving D)
    : disp_functor_axioms
        (psfunctor_fib_to_psfunctor_unit_disp_functor_inv_data D HD).
  Proof.
    split.
    - intros x xx ; cbn.
      apply maponpaths.
      unfold transportb.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z xx yy zz f g ff gg ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      use (cartesian_factorisation_unique (HD _ _ _ _)).
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite !transport_f_f.
      rewrite assoc_disp_var.
      rewrite !transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc_disp.
        rewrite cartesian_factorisation_commutes.
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite assoc_disp_var.
        rewrite cartesian_factorisation_commutes.
        rewrite mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        apply idpath.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_disp_functor_inv
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_functor
        (functor_identity C)
        D
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD)))).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor_inv_data D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor_inv_axioms D HD).
  Defined.

  Definition is_cartesian_psfunctor_fib_to_psfunctor_unit_disp_functor_inv
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : is_cartesian_disp_functor
        (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD).
  Proof.
    intros x y f xx yy ff Hff.
    cbn.
    use is_cartesian_indexed_cat.
    use is_z_iso_fiber_from_is_z_iso_disp.
    simple refine (_ ,, _ ,, _) ; cbn.
    - refine (cartesian_factorisation Hff (identity _) _).
      exact (transportb
               (λ z, _ -->[ z ] _)
               (id_left _)
               (HD x y f xx)).
    - use (cartesian_factorisation_unique (HD _ _ _ _)).
      unfold transportb.
      rewrite assoc_disp_var.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite cartesian_factorisation_commutes.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - use (cartesian_factorisation_unique Hff).
      unfold transportb.
      rewrite assoc_disp_var.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite cartesian_factorisation_commutes.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_cartesian_disp_functor_inv
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : cartesian_disp_functor
        (functor_identity C)
        D
        (indexed_cat_to_disp_cat
           (psfunctor_to_indexed_cat
              (indexed_cat_to_psfunctor
                 (cleaving_to_indexed_cat D HD)))).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD).
    - exact (is_cartesian_psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD).
  Defined.

  Definition psfunctor_fib_to_psfunctor_unit_equiv_unit_data
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_nat_trans_data
        (nat_trans_id (functor_identity C))
        (disp_functor_identity _)
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor D HD)
           (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD)).
  Proof.
    intros x xx ; cbn.
    refine (cartesian_factorisation
              (HD x x (identity x) xx)
              _
              (transportf
                 (λ z, _ -->[ z ] _)
                 _
                 (id_disp _))).
    exact (!(id_left _)).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_unit_equiv_unit_laws
              (D : disp_univalent_category C)
              (HD : cleaving D)
    : disp_nat_trans_axioms
        (psfunctor_fib_to_psfunctor_unit_equiv_unit_data D HD).
  Proof.
    intros x y f xx yy ff.
    cbn.
    unfold psfunctor_fib_to_psfunctor_unit_equiv_unit_data.
    rewrite !mor_disp_transportf_postwhisker.
    unfold transportb.
    rewrite !transport_f_f.
    use (cartesian_factorisation_unique (HD _ _ _ _)).
    rewrite !mor_disp_transportf_postwhisker.
    etrans.
    {
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        apply idpath.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite (transportf_indexed_cat_to_disp_cat
                 (psfunctor_to_indexed_cat
                    (indexed_cat_to_psfunctor
                       (cleaving_to_indexed_cat D HD)))).
      cbn.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply idtoiso_fiber_category.
      }
      rewrite !mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        apply idtoiso_disp_cartesian_lift.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite assoc_disp_var.
        rewrite cartesian_factorisation_commutes.
        apply idpath.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply idpath.
    }
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_equiv_unit
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_nat_trans
        (nat_trans_id (functor_identity C))
        (disp_functor_identity _)
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor D HD)
           (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD)).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_unit_data D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_unit_laws D HD).
  Defined.

  Definition psfunctor_fib_to_psfunctor_unit_equiv_counit_data
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_nat_trans_data
        (nat_trans_id (functor_identity C))
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD)
           (psfunctor_fib_to_psfunctor_unit_disp_functor D HD))
        (disp_functor_identity _)
    := λ x xx, id_disp _.

  Proposition psfunctor_fib_to_psfunctor_unit_equiv_counit_laws
              (D : disp_univalent_category C)
              (HD : cleaving D)
    : disp_nat_trans_axioms
        (psfunctor_fib_to_psfunctor_unit_equiv_counit_data D HD).
  Proof.
    intros x y f xx yy zz ; cbn.
    unfold psfunctor_fib_to_psfunctor_unit_equiv_counit_data.
    rewrite id_left_disp, id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_unit_equiv_counit
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : disp_nat_trans
        (nat_trans_id (functor_identity C))
        (disp_functor_over_id_composite
           (psfunctor_fib_to_psfunctor_unit_disp_functor_inv D HD)
           (psfunctor_fib_to_psfunctor_unit_disp_functor D HD))
        (disp_functor_identity _).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_counit_data D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_counit_laws D HD).
  Defined.

  (**
   7. The unit is a pointwise adjoint equivalence
   *)
  Definition psfunctor_fib_to_psfunctor_unit_equiv
             (D : disp_univalent_category C)
             (HD : cleaving D)
    : @left_equivalence
        (fib_slice_bicat C)
        _ _
        (psfunctor_fib_to_psfunctor_unit (D ,, HD)).
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (psfunctor_fib_to_psfunctor_unit_cartesian_disp_functor_inv D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_unit D HD).
    - exact (psfunctor_fib_to_psfunctor_unit_equiv_counit D HD).
    - cbn.
      use is_invertible_2cell_fib_slice.
      intros x xx.
      use is_z_iso_disp_indexed_cat_to_disp_cat.
      cbn ; cbn in xx.
      unfold psfunctor_fib_to_psfunctor_unit_equiv_unit_data.
      use is_z_iso_fiber_from_is_z_iso_disp.
      use (is_z_iso_disp_cartesian_factorisation
               (identity_is_z_iso x)
               (identity_is_z_iso x)).
      use (@is_z_iso_disp_transportf_fun_eq
             _ _
             _ _
             (identity_z_iso _)).
      apply id_is_z_iso_disp.
    - use is_invertible_2cell_fib_slice.
      intros x xx ; cbn.
      apply id_is_z_iso_disp.
  Defined.
End GrothendieckConstruction.
