(************************************************************************

 Grothendieck construction: the counit

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

 In this file, we construct the fourth part of this biequivalence, namely
 the counit.

 The counit gives a pseudotransformations between two endopseudofunctors
 on the bicategory of pseudofunctors. As such, for every object, we need
 to define a pseudotransformation. This is done in:
   [psfunctor_fib_to_psfunctor_counit_data_ob]
 In addition, we show that the counit is a pointwise adjoint equivalence.
 Since it is a pseudotransformation at every point, we must show that
 that particular pseudotransformation is a pointwise adjoint equivalence.
 This is done in:
   [equiv_psfunctor_fib_to_psfunctor_counit_data_ob_data_functor]
 Afterwards we construct invertible modifications that witness the
 naturality of this pseudotransformation. This is done in:
   [psfunctor_fib_to_psfunctor_counit_natural]
 Collecting all of these data and laws give us the desired
 pseudotransformation.

 Contents
 1. Action of the counit on objects
 2. Action of the counit on 1-cells
 3. The data of the counit
 4. The laws of the counit
 5. The counit

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

  (**
   1. Action of the counit on objects
   *)
  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : functor_data
        (fiber_category (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)) x)
        (F x : univalent_category).
  Proof.
    use make_functor_data.
    - exact (λ xx, xx).
    - intros xx yy ff.
      cbn in xx, yy, ff.
      exact (ff · pr1 ((psfunctor_id F x)^-1) yy).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_laws
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
              (x : C)
    : is_functor (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_data F x).
  Proof.
    split.
    - intros xx ; cbn -[psfunctor_id].
      exact (nat_trans_eq_pointwise (vcomp_rinv (psfunctor_id F x)) xx).
    - intros xx yy zz ff gg ; cbn -[psfunctor_id psfunctor_comp].
      cbn in xx, yy, zz, ff, gg.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (!(nat_trans_ax ((psfunctor_id F x)^-1) _ _ gg)).
      }
      assert (# F (identity x) ◃ (psfunctor_id F x)^-1
              =
              psfunctor_comp F (identity x) (identity x)
              • ##F (runitor _)
              • rinvunitor _)
        as p.
      {
        rewrite (psfunctor_F_runitor F (identity x)).
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite runitor_rinvunitor.
        rewrite id2_right.
        apply idpath.
      }
      pose (q := nat_trans_eq_pointwise p zz).
      cbn -[psfunctor_id psfunctor_comp] in q.
      rewrite id_right in q.
      etrans.
      {
        do 2 apply maponpaths.
        exact q.
      }
      refine (!_).
      etrans.
      {
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
      }
      rewrite !assoc'.
      do 3 apply maponpaths.
      refine (_ @ !(psfunctor_idtoiso F _ _)).
      do 3 apply maponpaths.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : bicat_of_univ_cats
        ⟦
          univalent_fiber_category
            (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)
             ,,
             is_univalent_disp_indexed_cat_to_disp_cat _)
            x
        ,
        F x ⟧.
  Proof.
    use make_functor.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_data F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_laws F x).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : functor_data
        (F x : univalent_category)
        (fiber_category (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)) x).
  Proof.
    use make_functor_data.
    - exact (λ xx, xx).
    - exact (λ xx yy ff, ff · pr11 (psfunctor_id F x) yy).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv_laws
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
              (x : C)
    : is_functor
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv_data F x).
  Proof.
    split.
    - intros xx.
      cbn -[psfunctor_id].
      apply id_left.
    - intros xx yy zz ff gg.
      cbn -[psfunctor_id psfunctor_comp].
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax (pr1 (psfunctor_id F x))).
      }
      cbn -[psfunctor_id psfunctor_comp].
      pose (nat_trans_eq_pointwise (psfunctor_rinvunitor F (identity x)) zz) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!_ @ !p).
        rewrite !assoc'.
        apply id_left.
      }
      etrans.
      {
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
      }
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (psfunctor_idtoiso F _ _).
      }
      refine (!(pr1_idtoiso_concat _ _) @ _).
      refine (_ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ h, pr1 (#F h) zz) _ _) @ _ @ maponpaths_idpath).
      apply maponpaths.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : (F x : univalent_category)
      ⟶
      fiber_category (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)) x.
  Proof.
    use make_functor.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv_data F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv_laws F x).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : nat_trans_data
        (functor_identity _)
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv F x)
    := λ _, identity _.

  Proposition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit_laws
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
              (x : C)
    : is_nat_trans
        _ _
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit_data F x).
  Proof.
    intros xx yy ff.
    cbn -[psfunctor_id psfunctor_comp].
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      do 2 apply maponpaths.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (nat_trans_eq_pointwise (vcomp_linv (psfunctor_id F x)) yy).
      }
      apply id_right.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(nat_trans_ax (pr1 (psfunctor_id F x)) _ _ ff)).
    }
    cbn -[psfunctor_id psfunctor_comp].
    pose (nat_trans_eq_pointwise (psfunctor_linvunitor F (identity x)) yy) as p.
    cbn -[psfunctor_id psfunctor_comp] in p.
    pose (nat_trans_eq_pointwise (psfunctor_rinvunitor F (identity x)) yy) as q.
    cbn -[psfunctor_id psfunctor_comp] in q.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_ @ !q).
      apply maponpaths_2.
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_ @ !p).
      apply maponpaths_2.
      apply id_left.
    }
    do 2 apply maponpaths.
    refine (psfunctor_idtoiso F _ _ @ _ @ !(psfunctor_idtoiso F _ _)).
    do 3 apply maponpaths.
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : functor_identity _
      ⟹
      psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x
      ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv F x.
  Proof.
    use make_nat_trans.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit_data F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit_laws F x).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : nat_trans_data
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv F x
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x)
        (functor_identity _)
    := λ _, identity _.

  Proposition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_laws
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
              (x : C)
    : is_nat_trans
        _ _
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_data F x).
  Proof.
    intros xx yy ff.
    cbn -[psfunctor_id psfunctor_comp].
    unfold psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_data.
    rewrite id_left, id_right.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (nat_trans_eq_pointwise (vcomp_rinv (psfunctor_id F x)) yy).
    }
    apply id_right.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv F x
      ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_data F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit_laws F x).
  Defined.

  Definition equiv_psfunctor_fib_to_psfunctor_counit_data_ob_data_functor
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             (x : C)
    : left_equivalence (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x).
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_inv F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_unit F x).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor_counit F x).
    - use is_nat_z_iso_to_is_invertible_2cell.
      intros xx.
      apply is_z_isomorphism_identity.
    - use is_nat_z_iso_to_is_invertible_2cell.
      intros xx.
      apply is_z_isomorphism_identity.
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             {x y : C}
             (f : y --> x)
    : nat_trans_data
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ # F f)
        (fiber_functor_from_cleaving
           (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
           (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F)) f
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F y)
    := λ _, identity _.

  Proposition psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_laws
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
              {x y : C}
              (f : y --> x)
    : is_nat_trans
        _ _
        (psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data F f).
  Proof.
    intros xx yy ff.
    cbn -[psfunctor_id psfunctor_comp].
    unfold psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data.
    unfold is_cartesian_indexed_cat_factorisation.
    cbn -[psfunctor_id psfunctor_comp].
    refine (id_right _ @ _ @ !(id_left _)).
    rewrite functor_id.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (id_right _ @ _).
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      apply id_left.
    }
    pose (nat_trans_eq_pointwise (psfunctor_F_runitor F f) yy) as p.
    cbn -[psfunctor_id psfunctor_comp] in p.
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      refine (!_ @ !p).
      apply id_right.
    }
    clear p.
    etrans.
    {
      apply maponpaths.
      apply psfunctor_idtoiso.
    }
    etrans.
    {
      apply maponpaths_2.
      apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
    }
    pose (nat_trans_eq_pointwise (psfunctor_F_lunitor F f) yy) as q.
    cbn -[psfunctor_id psfunctor_comp] in q.
    assert (# (pr1 (# F f)) (pr1 ((psfunctor_id F x) ^-1) yy)
            =
            pr11 (psfunctor_comp F (id₁ x) f) yy · pr1 (## F (lunitor _)) yy)
      as p.
    {
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact q.
      }
      rewrite !assoc.
      refine (id_right _ @ _ @ id_left _).
      apply maponpaths_2.
      exact (nat_trans_eq_pointwise (vcomp_rinv (psfunctor_comp F _ f)) yy).
    }
    refine (!_).
    refine (functor_comp _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact p.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply psfunctor_idtoiso.
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (_ @ pr1_idtoiso_concat _ _).
    do 2 apply maponpaths.
    refine (_ @ maponpathscomp0 (λ h, (psfunctor_to_indexed_cat F $ h) yy) _ _).
    apply maponpaths.
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             {x y : C}
             (f : y --> x)
    : nat_trans
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ # F f)
        (fiber_functor_from_cleaving
           (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
           (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F)) f
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F y).
  Proof.
    use make_nat_trans.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data F f).
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_laws F f).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_nat_z_iso
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
             {x y : C}
             (f : y --> x)
    : nat_z_iso
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ # F f)
        (fiber_functor_from_cleaving
           (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
           (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F)) f
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F y).
  Proof.
    use make_nat_z_iso.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans F f).
    - intro xx.
      apply is_z_isomorphism_identity.
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : pstrans_data
        (indexed_cat_to_psfunctor
           (cleaving_to_indexed_cat
              (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F),,
                 is_univalent_disp_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
              (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F))))
        F.
  Proof.
    use make_pstrans_data.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F).
    - intros x y f.
      use nat_z_iso_to_invertible_2cell.
      exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_z_iso F f).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data_data_on_ob
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : pstrans_from_cat_into_cat_data
        (indexed_cat_to_psfunctor
           (cleaving_to_indexed_cat
              (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F),,
                 is_univalent_disp_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
              (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F))))
        F.
  Proof.
    use make_pstrans_from_cat_into_cat_data.
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F).
    - intros x y f.
      exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_z_iso F f).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_counit_data_laws_on_ob
              (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : pstrans_from_cat_into_cat_laws
        (psfunctor_fib_to_psfunctor_counit_data_data_on_ob F).
  Proof.
    split.
    - intros x xx ; cbn -[psfunctor_id].
      unfold psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data.
      refine (id_right _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        cbn.
        unfold is_cartesian_indexed_cat_factorisation.
        cbn -[psfunctor_id psfunctor_comp].
        apply idpath.
      }
      rewrite functor_id.
      rewrite id_right.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          pose (p := nat_trans_eq_pointwise (psfunctor_F_runitor F (identity x)) xx).
          cbn -[psfunctor_id psfunctor_comp] in p.
          refine (_ @ !p).
          rewrite id_right.
          apply idpath.
        }
        apply psfunctor_idtoiso.
      }
      etrans.
      {
        apply maponpaths_2.
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
      }
      refine (assoc' _ _ _ @ _ @ id_right _).
      apply maponpaths.
      refine (!(pr1_idtoiso_concat _ _) @ _ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ z, pr1 (#(pr11 F) z) _) _ _) @ _).
      refine (_ @ @maponpaths_idpath _ _ (λ z, pr1 (#(pr11 F) z) _) _).
      apply maponpaths.
      apply homset_property.
    - intros x y z f g xx ; cbn -[psfunctor_id psfunctor_comp].
      unfold psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data.
      rewrite !id_right.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply functor_id.
      }
      rewrite id_left.
      etrans.
      {
        apply maponpaths_2.
        cbn.
        unfold is_cartesian_indexed_cat_factorisation.
        cbn -[psfunctor_comp].
        rewrite !functor_id.
        rewrite !id_right.
        apply maponpaths_2.
        apply maponpaths.
        apply id_left.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
      }
      refine (assoc' _ _ _ @ _ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        cbn in g, f.
        pose (p := nat_trans_eq_pointwise (psfunctor_F_runitor F (g · f)) xx).
        cbn -[psfunctor_id psfunctor_comp] in p.
        refine (_ @ !p).
        rewrite id_right.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        apply psfunctor_idtoiso.
      }
      refine (!(pr1_idtoiso_concat _ _) @ _ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ z, pr1 (#(pr11 F) z) _) _ _) @ _).
      refine (_ @ @maponpaths_idpath _ _ (λ z, pr1 (#(pr11 F) z) _) _).
      apply maponpaths.
      apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_data_ob
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : pstrans
        (indexed_cat_to_psfunctor
           (cleaving_to_indexed_cat
              (indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F),,
                 is_univalent_disp_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F))
              (indexed_cat_to_cleaving (psfunctor_to_indexed_cat F))))
        F.
  Proof.
    use pstrans_from_cat_into_cat.
    - exact (psfunctor_fib_to_psfunctor_counit_data_data_on_ob F).
    - exact (psfunctor_fib_to_psfunctor_counit_data_laws_on_ob F).
  Defined.

  (**
   2. Action of the counit on 1-cells
   *)
  Definition psfunctor_fib_to_psfunctor_counit_natural_nat_trans_data
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (τ : pstrans F G)
             (x : C)
    : nat_trans_data
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ (pr111 τ) x)
        (fiber_functor
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor τ))
           x
           ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor G x)
    := λ _, identity _.

  Proposition psfunctor_fib_to_psfunctor_counit_natural_nat_trans_laws
              {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
              (τ : pstrans F G)
              (x : C)
    : is_nat_trans
        _ _
        (psfunctor_fib_to_psfunctor_counit_natural_nat_trans_data τ x).
  Proof.
    intros xx yy ff.
    refine (id_right _ @ _).
    refine (_ @ !(id_left _)).
    cbn -[psfunctor_id].
    rewrite functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    pose (nat_trans_eq_pointwise (pstrans_id_inv τ x) yy) as p.
    cbn -[psfunctor_id] in p.
    rewrite !id_right in p.
    exact (!p).
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_natural_nat_trans
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (τ : pstrans F G)
             (x : C)
    : nat_trans
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ (pr111 τ) x)
        (fiber_functor
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor τ))
           x
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor G x).
  Proof.
    use make_nat_trans.
    - exact (psfunctor_fib_to_psfunctor_counit_natural_nat_trans_data τ x).
    - exact (psfunctor_fib_to_psfunctor_counit_natural_nat_trans_laws τ x).
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_natural_nat_z_iso
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (τ : pstrans F G)
             (x : C)
    : nat_z_iso
        (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x ∙ (pr111 τ) x)
        (fiber_functor
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor τ))
           x
         ∙ psfunctor_fib_to_psfunctor_counit_data_ob_data_functor G x).
  Proof.
    use make_nat_z_iso.
    - exact (psfunctor_fib_to_psfunctor_counit_natural_nat_trans τ x).
    - intro.
      apply is_z_isomorphism_identity.
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_natural_data
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (τ : pstrans F G)
    : invertible_modification_data
        (psfunctor_fib_to_psfunctor_counit_data_ob F · τ)
        (indexed_functor_to_pstrans
           (cartesian_disp_functor_to_indexed_functor
              _ _
              (psfunctor_psfunctor_bicat_to_fib_mor C τ))
         · psfunctor_fib_to_psfunctor_counit_data_ob G).
  Proof.
    intro x.
    use nat_z_iso_to_invertible_2cell.
    exact (psfunctor_fib_to_psfunctor_counit_natural_nat_z_iso τ x).
  Defined.

  Proposition psfunctor_fib_to_psfunctor_counit_natural_laws
              {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
              (τ : pstrans F G)
    : is_modification (psfunctor_fib_to_psfunctor_counit_natural_data τ).
  Proof.
    intros x y f.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intros xx.
    cbn -[psfunctor_id psfunctor_comp].
    unfold psfunctor_fib_to_psfunctor_counit_natural_nat_trans_data.
    unfold psfunctor_fib_to_psfunctor_counit_data_ob_nat_trans_data.
    cbn in x, y, f, xx.
    etrans.
    {
      do 2 refine (id_right _ @ _).
      apply maponpaths_2.
      refine (id_right _ @ _).
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      refine (functor_id (pr111 τ y) _).
    }
    refine (id_right _ @ _).
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply functor_id.
      }
      refine (id_left _ @ _).
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (id_right _ @ _).
        apply id_left.
      }
      apply id_left.
    }
    unfold is_cartesian_indexed_cat_factorisation.
    unfold is_cartesian_to_iso_indexed_cat_inv.
    cbn -[psfunctor_id psfunctor_comp].
    unfold is_cartesian_indexed_cat_factorisation.
    cbn -[psfunctor_id psfunctor_comp].
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply functor_id.
        }
        apply id_right.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        rewrite assoc'.
        etrans.
        {
          apply maponpaths.
          exact (nat_trans_eq_pointwise
                   (vcomp_rinv (psfunctor_comp F f (identity y)))
                   xx).
        }
        apply id_right.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (nat_trans_eq_pointwise
                   (vcomp_rinv (psfunctor_id F y))
                   _).
        }
        apply functor_id.
      }
      apply id_right.
    }
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply (nat_trans_ax ((psfunctor_id G y) ^-1)).
    }
    refine (_ @ id_left _).
    do 2 refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (transportf_psfunctor_into_cat _ _ _ _ @ _).
      apply id_left.
    }
    pose (nat_trans_eq_pointwise (psfunctor_F_runitor G f) (pr1 ((pr111 τ) x) xx)) as p.
    cbn -[psfunctor_id psfunctor_comp] in p.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (_ @ !p).
      apply (!(id_right _)).
    }
    refine (!(nat_trans_eq_pointwise (psfunctor_vcomp G _ _) _) @ _).
    refine (_ @ nat_trans_eq_pointwise (psfunctor_id2 G _) _).
    refine (maponpaths (λ z, pr1 (##G z) _) _).
    apply homset_property.
  Qed.

  Definition psfunctor_fib_to_psfunctor_counit_natural
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (τ : pstrans F G)
    : invertible_2cell
        (psfunctor_fib_to_psfunctor_counit_data_ob F · τ)
        (indexed_functor_to_pstrans
           (cartesian_disp_functor_to_indexed_functor
              _ _
              (psfunctor_psfunctor_bicat_to_fib_mor C τ))
         · psfunctor_fib_to_psfunctor_counit_data_ob G).
  Proof.
    use make_invertible_modification.
    - exact (psfunctor_fib_to_psfunctor_counit_natural_data τ).
    - exact (psfunctor_fib_to_psfunctor_counit_natural_laws τ).
  Defined.

  (**
   3. The data of the counit
   *)
  Definition psfunctor_fib_to_psfunctor_counit_data
    : pstrans_data
        (comp_psfunctor
           (psfunctor_fib_to_psfunctor_bicat C)
           (psfunctor_psfunctor_bicat_to_fib C))
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - exact psfunctor_fib_to_psfunctor_counit_data_ob.
    - exact @psfunctor_fib_to_psfunctor_counit_natural.
  Defined.

  (**
   4. The laws of the counit
   *)
  Proposition psfunctor_fib_to_psfunctor_counit_is_pstrans
    : is_pstrans psfunctor_fib_to_psfunctor_counit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros F₁ F₂ n₁ n₂ m.
      Opaque comp_psfunctor.
      use modification_eq.
      Transparent comp_psfunctor.
      intro x.
      use nat_trans_eq ; [ apply homset_property | ].
      intros xx.
      refine (id_right _ @ _).
      cbn -[psfunctor_id].
      refine (_ @ !(id_left _)).
      refine (!_).
      refine (_ @ id_right _).
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (nat_trans_eq_pointwise
               (vcomp_rinv (psfunctor_id F₂ x))
               (pr1 (pr111 n₂ x) xx)).
    - intros F.
      Opaque comp_psfunctor.
      use modification_eq.
      Transparent comp_psfunctor.
      intro x.
      use nat_trans_eq ; [ apply homset_property | ].
      intros xx.
      refine (id_right _ @ _).
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply id_left.
      }
      refine (id_left _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (transportf_indexed_cat_to_disp_cat
                 (psfunctor_to_indexed_cat F)).
      }
      unfold psfunctor_psfunctor_bicat_to_fib_id_data.
      refine (_ @ nat_trans_eq_pointwise (vcomp_rinv (psfunctor_id F x)) xx).
      cbn -[psfunctor_id].
      do 3 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (_ @ id_left _).
      do 2 refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          pose (p := nat_trans_eq_pointwise (psfunctor_linvunitor F (identity x)) xx).
          cbn -[psfunctor_id psfunctor_comp] in p.
          refine (_ @ !p).
          apply maponpaths_2.
          exact (!(id_left _)).
        }
        apply psfunctor_idtoiso.
      }
      refine (!(pr1_idtoiso_concat _ _) @ _ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ h, pr1 (#(F : psfunctor _ _) h) xx) _ _) @ _).
      refine (_ @ @maponpaths_idpath _ _ (λ h, pr1 (#(F : psfunctor _ _) h) xx) _).
      apply maponpaths.
      apply homset_property.
    - intros F₁ F₂ F₃ τ θ.
      Opaque comp_psfunctor.
      use modification_eq.
      Transparent comp_psfunctor.
      intro x.
      use nat_trans_eq ; [ apply homset_property | ].
      intros xx.
      refine (id_right _ @ _).
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        do 3 refine (id_right _ @ _).
        etrans.
        {
          apply maponpaths.
          apply functor_id.
        }
        apply id_right.
      }
      refine (id_left _ @ _).
      unfold psfunctor_psfunctor_bicat_to_fib_comp_data.
      cbn -[psfunctor_id].
      etrans.
      {
        apply maponpaths_2.
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F₃)).
      }
      refine (_ @ nat_trans_eq_pointwise (vcomp_rinv (psfunctor_id F₃ x)) _).
      cbn -[psfunctor_id].
      do 3 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (_ @ id_left _).
      do 2 refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          pose (p := nat_trans_eq_pointwise
                       (psfunctor_linvunitor F₃ (identity x))
                       (pr1 (pr111 θ x) (pr1 (pr111 τ x) xx))).
          cbn -[psfunctor_id psfunctor_comp] in p.
          refine (_ @ !p).
          apply maponpaths_2.
          exact (!(id_left _)).
        }
        apply psfunctor_idtoiso.
      }
      refine (!(pr1_idtoiso_concat _ _) @ _ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ h, pr1 (#(F₃ : psfunctor _ _) h) _) _ _) @ _).
      refine (_ @ @maponpaths_idpath _ _ (λ h, pr1 (#(F₃ : psfunctor _ _) h) _) _).
      apply maponpaths.
      apply homset_property.
      Opaque comp_psfunctor.
  Qed.
  Transparent comp_psfunctor.

  (**
   5. The counit
   *)
  Definition psfunctor_fib_to_psfunctor_counit
    : pstrans
        (comp_psfunctor
           (psfunctor_fib_to_psfunctor_bicat C)
           (psfunctor_psfunctor_bicat_to_fib C))
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact psfunctor_fib_to_psfunctor_counit_data.
    - exact psfunctor_fib_to_psfunctor_counit_is_pstrans.
  Defined.
End GrothendieckConstruction.
