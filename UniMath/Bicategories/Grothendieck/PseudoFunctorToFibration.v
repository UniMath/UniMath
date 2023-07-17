(************************************************************************

 The Grothendieck Construction

 The Grothendieck construction gives a biequivalence between the
 bicategory of fibrations over a fixed category `C` and the bicategory
 of indexd categories over `C`. In this file, our goal is to construct
 this particular equivalence. Except for some laws, this file collects
 constructions already given elsewhere in UniMath.

 Note: at this moment, the construction is not complete yet, because we
 need to construct a biequivalence between the bicategory of fibrations
 on `C` and the bicategory of indexed categories. We currently only have
 the pseudofunctor from fibrations to indexed categories.

 Contents
 1. The action on pseudofunctors
 2. The action on pseudotransformations
 3. The action on modifications
 4. The identitor
 5. The compositor
 6. The data
 7. The laws
 8. The pseudofunctor from pseudofunctors to fibrations

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
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PseudoFunctorsIntoCat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.PseudoTransformationIntoCat.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.ModificationIntoCat.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.

Local Open Scope cat.

Definition TODO { A : UU } : A.
Admitted.

Local Open Scope cat.

Section GrothendieckConstruction.
  Context (C : univalent_category).

  (**
   1. The action on pseudofunctors
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_ob
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : fib_slice_bicat C
    := let Φ := psfunctor_to_indexed_cat F in
       (indexed_cat_to_disp_cat Φ
       ,, is_univalent_disp_indexed_cat_to_disp_cat Φ)
       ,, indexed_cat_to_cleaving Φ.

  (**
   2. The action on pseudotransformations
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_mor
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (n : pstrans F G)
    : psfunctor_psfunctor_bicat_to_fib_ob F
      -->
      psfunctor_psfunctor_bicat_to_fib_ob G
    := let τ := pstrans_to_indexed_functor n in
       indexed_functor_to_cartesian_disp_functor τ.

  (**
   3. The action on modifications
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_cell
             {F G : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             {n₁ n₂ : pstrans F G}
             (w : modification n₁ n₂)
    : psfunctor_psfunctor_bicat_to_fib_mor n₁
      ==>
      psfunctor_psfunctor_bicat_to_fib_mor n₂
    := let m := modification_to_indexed_nat_trans w in
       indexed_nat_trans_to_disp_nat_trans m.

  Arguments psfunctor_psfunctor_bicat_to_fib_cell {_ _ _ _} _ /.

  (**
   4. The identitor
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_id_data
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_identity _)
        (pr1 (psfunctor_psfunctor_bicat_to_fib_mor (id_pstrans F)))
    := λ x xx, pr11 (psfunctor_id F x) xx.

  Arguments psfunctor_psfunctor_bicat_to_fib_id_data _ /.

  Proposition psfunctor_psfunctor_bicat_to_fib_id_laws
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : disp_nat_trans_axioms (psfunctor_psfunctor_bicat_to_fib_id_data F).
  Proof.
    intros x y f xx yy ff ; cbn -[psfunctor_id psfunctor_comp].
    pose (p := nat_trans_eq_pointwise (psfunctor_linvunitor F f) yy).
    cbn -[psfunctor_id psfunctor_comp] in p.
    rewrite id_left in p.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      exact (!p).

    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply id_right.
        }
        apply id_right.
      }
      exact (!(nat_trans_ax (pr1 (psfunctor_id F x)) _ _ ff)).
    }
    cbn -[psfunctor_id psfunctor_comp].
    pose (q := nat_trans_eq_pointwise (psfunctor_rinvunitor F f) yy).
    cbn -[psfunctor_id psfunctor_comp] in q.
    rewrite assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (_ @ !q).
      apply maponpaths_2.
      exact (!(id_left _)).
    }
    etrans.
    {
      apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat F)).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply psfunctor_idtoiso.
    }
    refine (_ @ !(psfunctor_idtoiso F _ _)).
    refine (!(pr1_idtoiso_concat _ _) @ _).
    do 2 apply maponpaths.
    refine (!(maponpathscomp0 (λ h, pr1 (#F h) yy) _ _) @ _).
    apply maponpaths.
    apply homset_property.
  Qed.

  Definition psfunctor_psfunctor_bicat_to_fib_id
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_identity _)
        (pr1 (psfunctor_psfunctor_bicat_to_fib_mor (id_pstrans F))).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_psfunctor_bicat_to_fib_id_data F).
    - exact (psfunctor_psfunctor_bicat_to_fib_id_laws F).
  Defined.

  (**
   5. The compositor
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_comp_data
             {F G H : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (n₁ : pstrans F G)
             (n₂ : pstrans G H)
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor n₁))
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor n₂)))
        (indexed_functor_to_disp_functor_data (pstrans_to_indexed_functor (n₁ · n₂)))
    := λ x xx, pr11 (psfunctor_id H x) _.

  Arguments psfunctor_psfunctor_bicat_to_fib_comp_data {_ _ _} _ _ _ /.

  Proposition psfunctor_psfunctor_bicat_to_fib_comp_axioms
              {F G H : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
              (n₁ : pstrans F G)
              (n₂ : pstrans G H)
    : disp_nat_trans_axioms (psfunctor_psfunctor_bicat_to_fib_comp_data n₁ n₂).
  Proof.
    intros x y f xx yy ff ; cbn -[psfunctor_id psfunctor_comp].
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      do 3 apply maponpaths.
      refine (id_left _ @ _).
      apply maponpaths.
      refine (id_left _ @ _).
      apply id_right.
    }
    etrans.
    {
      apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat H)).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax (pr1 (psfunctor_id H x))).
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      apply functor_comp.
    }
    do 3 refine (assoc' _ _ _ @ _).
    refine (!_).
    do 3 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    do 2 apply maponpaths.
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (_ @ !(nat_trans_eq_pointwise (psfunctor_rinvunitor H f) _)).
      refine (_ @ assoc _ _ _).
      exact (!(id_left _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply psfunctor_idtoiso.
    }
    refine (!(pr1_idtoiso_concat _ _) @ _).
    refine (!_).
    etrans.
    {
      refine (_ @ !(nat_trans_eq_pointwise (psfunctor_linvunitor H f) _)).
      refine (_ @ assoc _ _ _).
      exact (!(id_left _)).
    }
    etrans.
    {
      apply psfunctor_idtoiso.
    }
    do 2 apply maponpaths.
    refine (_ @ maponpathscomp0 (λ z, pr1 (#H z) _) _ _).
    apply maponpaths.
    apply homset_property.
    (* Qed. *)
  Admitted.

  Definition psfunctor_psfunctor_bicat_to_fib_comp
             {F G H : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
             (n₁ : pstrans F G)
             (n₂ : pstrans G H)
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor n₁))
           (indexed_functor_to_disp_functor (pstrans_to_indexed_functor n₂)))
        (indexed_functor_to_disp_functor_data (pstrans_to_indexed_functor (n₁ · n₂))).
  Proof.
    simple refine (_ ,, _).
    - exact (psfunctor_psfunctor_bicat_to_fib_comp_data n₁ n₂).
    - exact (psfunctor_psfunctor_bicat_to_fib_comp_axioms n₁ n₂).
  Defined.

  (**
   6. The data
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_data
    : psfunctor_data
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats)
        (fib_slice_bicat C).
  Proof.
    use make_psfunctor_data.
    - exact psfunctor_psfunctor_bicat_to_fib_ob.
    - exact (λ F G n, psfunctor_psfunctor_bicat_to_fib_mor n).
    - exact (λ F G n₁ n₂ w, psfunctor_psfunctor_bicat_to_fib_cell w).
    - exact (λ F, psfunctor_psfunctor_bicat_to_fib_id F).
    - exact (λ F G H n₁ n₂, psfunctor_psfunctor_bicat_to_fib_comp n₁ n₂).
  Defined.

  (**
   7. The laws
   *)
  Proposition psfunctor_psfunctor_bicat_to_fib_laws
    : psfunctor_laws psfunctor_psfunctor_bicat_to_fib_data.
  Proof.
    repeat split.
    - intros F G n.
      use disp_nat_trans_eq.
      intros x xx.
      apply id_left.
    - intros F G n₁ n₂ n₃ w₁ w₂.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (pr1 (psfunctor_id G x))).
        }
        rewrite !assoc'.
        apply maponpaths.
        pose (nat_trans_eq_pointwise
                (psfunctor_rinvunitor G (identity x))
                (pr1 (pr111 n₃ x) xx)) as p.
        cbn -[psfunctor_id psfunctor_comp] in p.
        refine (!(p @ _)).
        apply maponpaths_2.
        apply id_left.
      }
      etrans.
      {
        apply (transportf_indexed_cat_to_disp_cat (psfunctor_to_indexed_cat G)).
      }
      cbn -[psfunctor_id psfunctor_comp].
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply psfunctor_idtoiso.
      }
      refine (!(pr1_idtoiso_concat _ _) @ _).
      refine (_ @ idtoiso_idpath _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ z, pr1 (#(pr11 G) z) _) _ _) @ _).
      refine (_ @ @maponpaths_idpath _ _ (λ z, pr1 (#(pr11 G) z) _) _).
      apply maponpaths.
      apply homset_property.
    - intros F G n.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      apply TODO.
    - intros F G n.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      apply TODO.
    - intros F₁ F₂ F₃ F₄ n₁ n₂ n₃.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      apply TODO.
    - intros F₁ F₂ F₃ n m₁ m₂ w.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      apply TODO.
    - intros F₁ F₂ F₃ n₁ n₂ m w.
      use disp_nat_trans_eq.
      intros x xx.
      cbn -[psfunctor_id psfunctor_comp].
      apply TODO.
  Qed.

  fsdfdffd

  Definition psfunctor_psfunctor_bicat_to_fib_invertible_cells
    : invertible_cells psfunctor_psfunctor_bicat_to_fib_data.
  Proof.
    split.
    - intro F.
      use is_invertible_2cell_fib_slice.
      intros x xx.
      simple refine (transportf
                       (λ z, is_z_iso_disp _ z)
                       _
                       (indexed_cat_to_disp_cat_to_disp_iso
                          (psfunctor_to_indexed_cat F)
                          _ _ _ _)).
      + apply id_left.
      + apply is_z_isomorphism_identity.
    - intros F G H n₁ n₂.
      use is_invertible_2cell_fib_slice.
      intros x xx.
      simple refine (transportf
                       (λ z, is_z_iso_disp _ z)
                       _
                       (indexed_cat_to_disp_cat_to_disp_iso
                          (psfunctor_to_indexed_cat H)
                          _ _ _ _)).
      + apply id_left.
      + apply is_z_isomorphism_identity.
  Qed.

  (**
   8. The pseudofunctor from pseudofunctors to fibrations
   *)
  Definition psfunctor_psfunctor_bicat_to_fib
    : psfunctor
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats)
        (fib_slice_bicat C).
  Proof.
    use make_psfunctor.
    - exact psfunctor_psfunctor_bicat_to_fib_data.
    - exact psfunctor_psfunctor_bicat_to_fib_laws.
    - exact psfunctor_psfunctor_bicat_to_fib_invertible_cells.
  Defined.
End GrothendieckConstruction.
