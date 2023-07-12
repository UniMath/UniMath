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
 1. From fibrations to pseudofunctors
 1.1. Preservation of the identity
 1.2. Preservation of composition
 1.3. The data
 1.4. The laws
 1.5. Pseudofunctor from fibrations to pseudofunctors
 2. From pseudofunctors to fibrations
 2.1. The action on pseudofunctors
 2.2. The action on pseudotransformations
 2.3. The action on modifications
 2.4. The identitor
 2.5. The compositor
 2.6. The data
 2.7. The laws
 2.8. The pseudofunctor from pseudofunctors to fibrations
 3. The unit
 4. The counit
 5. The biequivalence

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
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.

Local Open Scope cat.

Definition TODO { A : UU } : A.
Admitted.

(**
 1. From fibrations to pseudofunctors
 *)

(**
 1.1. Preservation of the identity
 *)
Definition psfunctor_id_fib_to_psfunctor_bicat_data
           {C : univalent_category}
           (D : disp_univalent_category C)
           (HD : cleaving D)
  : invertible_modification_data
      (id_pstrans
         (indexed_cat_to_psfunctor (cleaving_to_indexed_cat D HD)))
      (indexed_functor_to_pstrans
         (cartesian_disp_functor_to_indexed_functor
            HD
            HD
            (disp_functor_identity D
             ,,
             disp_functor_identity_is_cartesian_disp_functor D))).
Proof.
  intro x.
  use nat_z_iso_to_invertible_2cell.
  exact (fiber_functor_identity D x).
Defined.

Proposition psfunctor_id_fib_to_psfunctor_bicat_laws
           {C : univalent_category}
           (D : disp_univalent_category C)
           (HD : cleaving D)
  : is_modification (psfunctor_id_fib_to_psfunctor_bicat_data D HD).
Proof.
  intros x y f.
  use nat_trans_eq ; [ apply homset_property | ].
  intros xx ; cbn.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  use (cartesian_factorisation_unique (HD _ _ _ _)).
  rewrite mor_disp_transportf_postwhisker.
  rewrite id_left_disp.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite id_left_disp.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite id_left_disp.
  unfold transportb.
  rewrite transport_f_f.
  refine (!_).
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition psfunctor_id_fib_to_psfunctor_bicat
           {C : univalent_category}
           (D : disp_univalent_category C)
           (HD : cleaving D)
  : invertible_modification
      (id_pstrans
         (indexed_cat_to_psfunctor (cleaving_to_indexed_cat D HD)))
      (indexed_functor_to_pstrans
         (cartesian_disp_functor_to_indexed_functor
            HD
            HD
            (disp_functor_identity D
             ,,
             disp_functor_identity_is_cartesian_disp_functor D))).
Proof.
  use make_invertible_modification.
  - exact (psfunctor_id_fib_to_psfunctor_bicat_data D HD).
  - exact (psfunctor_id_fib_to_psfunctor_bicat_laws D HD).
Defined.

(**
 1.2. Preservation of composition
 *)
Definition psfunctor_comp_fib_to_psfunctor_bicat_data
           {C : univalent_category}
           {D₁ D₂ D₃ : disp_univalent_category C}
           (HD₁ : cleaving D₁)
           (HD₂ : cleaving D₂)
           (HD₃ : cleaving D₃)
           (F : cartesian_disp_functor (functor_identity C) D₁ D₂)
           (G : cartesian_disp_functor (functor_identity C) D₂ D₃)
  : invertible_modification_data
      (comp_pstrans
         (indexed_functor_to_pstrans
            (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F))
         (indexed_functor_to_pstrans
            (cartesian_disp_functor_to_indexed_functor HD₂ HD₃ G)))
      (indexed_functor_to_pstrans
         (cartesian_disp_functor_to_indexed_functor
            HD₁ HD₃
            (disp_functor_over_id_composite F G
             ,,
             disp_functor_over_id_composite_is_cartesian (pr2 F) (pr2 G)))).
Proof.
  intro x.
  use nat_z_iso_to_invertible_2cell.
  exact (fiber_functor_comp F G x).
Defined.

Proposition psfunctor_comp_fib_to_psfunctor_bicat_laws
            {C : univalent_category}
            {D₁ D₂ D₃ : disp_univalent_category C}
            (HD₁ : cleaving D₁)
            (HD₂ : cleaving D₂)
            (HD₃ : cleaving D₃)
            (F : cartesian_disp_functor (functor_identity C) D₁ D₂)
            (G : cartesian_disp_functor (functor_identity C) D₂ D₃)
  : is_modification (psfunctor_comp_fib_to_psfunctor_bicat_data HD₁ HD₂ HD₃ F G).
Proof.
  intros x y f.
  use nat_trans_eq ; [ apply homset_property | ].
  intros xx ; cbn.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite id_left_disp.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  use (cartesian_factorisation_unique
         (disp_functor_over_id_composite_is_cartesian (pr2 F) (pr2 G)
            _ _ _ _ _ _
            (HD₁ _ _ _ _))).
  rewrite !mor_disp_transportf_postwhisker.
  cbn.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  etrans.
  {
    do 2 apply maponpaths.
    refine (!_).
    apply (disp_functor_comp_var G).
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite disp_functor_transportf.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite transport_f_f.
  refine (!_).
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition psfunctor_comp_fib_to_psfunctor_bicat
           {C : univalent_category}
           {D₁ D₂ D₃ : disp_univalent_category C}
           (HD₁ : cleaving D₁)
           (HD₂ : cleaving D₂)
           (HD₃ : cleaving D₃)
           (F : cartesian_disp_functor (functor_identity C) D₁ D₂)
           (G : cartesian_disp_functor (functor_identity C) D₂ D₃)
  : invertible_modification
      (comp_pstrans
         (indexed_functor_to_pstrans
            (cartesian_disp_functor_to_indexed_functor HD₁ HD₂ F))
         (indexed_functor_to_pstrans
            (cartesian_disp_functor_to_indexed_functor HD₂ HD₃ G)))
      (indexed_functor_to_pstrans
         (cartesian_disp_functor_to_indexed_functor
            HD₁ HD₃
            (disp_functor_over_id_composite F G
             ,,
             disp_functor_over_id_composite_is_cartesian (pr2 F) (pr2 G)))).
Proof.
  use make_invertible_modification.
  - exact (psfunctor_comp_fib_to_psfunctor_bicat_data HD₁ HD₂ HD₃ F G).
  - exact (psfunctor_comp_fib_to_psfunctor_bicat_laws HD₁ HD₂ HD₃ F G).
Defined.

Section GrothendieckConstruction.
  Context (C : univalent_category).

  (**
   1.3. The data
   *)
  Definition psfunctor_fib_to_psfunctor_bicat_data
    : psfunctor_data
        (fib_slice_bicat C)
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats).
  Proof.
    use make_psfunctor_data.
    - exact (λ P,
             indexed_cat_to_psfunctor
               (cleaving_to_indexed_cat
                  (pr1 P)
                  (pr2 P))).
    - exact (λ P₁ P₂ F,
             indexed_functor_to_pstrans
               (cartesian_disp_functor_to_indexed_functor
                  (pr2 P₁)
                  (pr2 P₂)
                  F)).
    - exact (λ P₁ P₂ F G τ,
             indexed_nat_trans_to_modification
               (disp_nat_trans_to_indexed_nat_trans
                  (pr2 P₁)
                  (pr2 P₂)
                  τ)).
    - exact (λ P, pr1 (psfunctor_id_fib_to_psfunctor_bicat (pr1 P) (pr2 P))).
    - exact (λ P₁ P₂ P₃ F G, pr1 (psfunctor_comp_fib_to_psfunctor_bicat _ _ _ F G)).
  Defined.

  (**
   1.4. The laws
   *)
  Proposition psfunctor_fib_to_psfunctor_bicat_laws
    : psfunctor_laws psfunctor_fib_to_psfunctor_bicat_data.
  Proof.
    repeat split.
    - intros P₁ P₂ F.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      apply idpath.
    - intros P₁ P₂ F G H τ θ.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      apply maponpaths_2.
      apply homset_property.
    - intros P₁ P₂ F.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite (disp_functor_id (pr1 F)).
      unfold transportb.
      rewrite !transport_f_f.
      refine (!_).
      apply transportf_set.
      apply homset_property.
    - intros P₁ P₂ F.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      refine (!_).
      apply transportf_set.
      apply homset_property.
    - intros P₁ P₂ P₃ P₄ F G H.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite (disp_functor_id (pr1 H)).
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros P₁ P₂ P₃ F G₁ G₂ τ.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros P₁ P₂ P₃ F₁ F₂ G τ.
      use modification_eq.
      intros x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro xx.
      cbn.
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition invertible_cells_psfunctor_fib_to_psfunctor_bicat
    : invertible_cells psfunctor_fib_to_psfunctor_bicat_data.
  Proof.
    split.
    - intro P.
      exact (property_from_invertible_2cell
               (psfunctor_id_fib_to_psfunctor_bicat (pr1 P) (pr2 P))).
    - intros P₁ P₂ P₃ F G.
      exact (property_from_invertible_2cell
               (psfunctor_comp_fib_to_psfunctor_bicat _ _ _ F G)).
  Defined.

  (**
   1.5. Pseudofunctor from fibrations to pseudofunctors
   *)
  Definition psfunctor_fib_to_psfunctor_bicat
    : psfunctor
        (fib_slice_bicat C)
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats).
  Proof.
    use make_psfunctor.
    - exact psfunctor_fib_to_psfunctor_bicat_data.
    - exact psfunctor_fib_to_psfunctor_bicat_laws.
    - exact invertible_cells_psfunctor_fib_to_psfunctor_bicat.
  Defined.

  (**
   2. From pseudofunctors to fibrations
   *)

  (**
   2.1. The action on pseudofunctors
   *)
  Definition psfunctor_psfunctor_bicat_to_fib_ob
             (F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats)
    : fib_slice_bicat C
    := let Φ := psfunctor_to_indexed_cat F in
       (indexed_cat_to_disp_cat Φ
       ,, is_univalent_disp_indexed_cat_to_disp_cat Φ)
       ,, indexed_cat_to_cleaving Φ.

  (**
   2.2. The action on pseudotransformations
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
   2.3. The action on modifications
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
   2.4. The identitor
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
   2.5. The compositor
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
    apply TODO.
  Qed.

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
   2.6. The data
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
   2.7. The laws
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
      apply TODO.
    - intros F G n.
      use disp_nat_trans_eq.
      intros x xx.
      apply TODO.
    - intros F G n.
      use disp_nat_trans_eq.
      intros x xx.
      apply TODO.
    - intros F₁ F₂ F₃ F₄ n₁ n₂ n₃.
      use disp_nat_trans_eq.
      intros x xx.
      apply TODO.
    - intros F₁ F₂ F₃ n m₁ m₂ w.
      use disp_nat_trans_eq.
      intros x xx.
      apply TODO.
    - intros F₁ F₂ F₃ n₁ n₂ m w.
      use disp_nat_trans_eq.
      intros x xx.
      apply TODO.
  Qed.

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
   2.8. The pseudofunctor from pseudofunctors to fibrations
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

  (**
   3. The unit
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

  Definition psfunctor_fib_to_psfunctor_unit_data
    : pstrans_data
        (comp_psfunctor
           psfunctor_psfunctor_bicat_to_fib
           psfunctor_fib_to_psfunctor_bicat)
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
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply TODO.
    - intros P₁ P₂ P₃ F G.
      use disp_nat_trans_eq.
      intros x xx.
      cbn ; unfold psfunctor_fib_to_psfunctor_unit_natural_data.
      apply TODO.
  Admitted.

  Definition psfunctor_fib_to_psfunctor_unit
    : pstrans
        (comp_psfunctor
           psfunctor_psfunctor_bicat_to_fib
           psfunctor_fib_to_psfunctor_bicat)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact psfunctor_fib_to_psfunctor_unit_data.
    - exact is_pstrans_psfunctor_fib_to_psfunctor_unit.
  Defined.

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
    - simple refine (_ ,, _).
      + intros x xx ; cbn.
        refine (cartesian_factorisation
                  (HD x x (identity x) xx)
                  _
                  (transportf
                     (λ z, _ -->[ z ] _)
                     _
                     (id_disp _))).
        exact (!(id_left _)).
      + apply TODO.
    - simple refine (_ ,, _).
      + exact (λ x xx, id_disp _).
      + (*intros x y f xx yy zz ; cbn.
        rewrite id_left_disp, id_right_disp.
        unfold transportb.
        rewrite !transport_f_f.
        rewrite cartesian_factorisation_commutes.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply homset_property.*)
        apply TODO.
    - use is_invertible_2cell_fib_slice.
      intros x xx ; cbn.
      apply TODO.
    - use is_invertible_2cell_fib_slice.
      intros x xx ; cbn.
      apply id_is_z_iso_disp.
  Defined.

  (**
   4. The counit
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
    - exact (psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F).
    - intros x y f.
      exact (psfunctor_fib_to_psfunctor_counit_data_ob_nat_z_iso F f).
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
      cbn.
      apply TODO.
    - apply TODO.
  Defined.

  Definition psfunctor_fib_to_psfunctor_counit_data
    : pstrans_data
        (comp_psfunctor
           psfunctor_fib_to_psfunctor_bicat
           psfunctor_psfunctor_bicat_to_fib)
        (id_psfunctor _).
  Proof.
    use make_pstrans_data.
    - exact psfunctor_fib_to_psfunctor_counit_data_ob.
    - intros F G n.
      use make_invertible_modification.
      + intros x.
        use nat_z_iso_to_invertible_2cell.
        use make_nat_z_iso.
        * use make_nat_trans.
          ** intros xx.
             cbn.
             apply identity.
          ** apply TODO.
        * apply TODO.
      + apply TODO.
        (*intros x y f.
        use nat_trans_eq ; [ apply homset_property | ].
        intro xx.
        cbn.*)
  Defined.

  Proposition psfunctor_fib_to_psfunctor_counit_is_pstrans
    : is_pstrans psfunctor_fib_to_psfunctor_counit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - intros F₁ F₂ n₁ n₂ m.
      use modification_eq.
      intro x.
      use nat_trans_eq ; [ apply homset_property | ].
      intros xx.
      apply TODO.
    - apply TODO.
    - apply TODO.
      Opaque comp_psfunctor.
  Qed.
  Transparent comp_psfunctor.

  Definition psfunctor_fib_to_psfunctor_counit
    : pstrans
        (comp_psfunctor
           psfunctor_fib_to_psfunctor_bicat
           psfunctor_psfunctor_bicat_to_fib)
        (id_psfunctor _).
  Proof.
    use make_pstrans.
    - exact psfunctor_fib_to_psfunctor_counit_data.
    - exact psfunctor_fib_to_psfunctor_counit_is_pstrans.
  Defined.

  (**
   5. The biequivalence
   *)
  Definition psfunctor_fib_to_psfunctor_bicat_unit_counit
    : is_biequivalence_unit_counit
        psfunctor_fib_to_psfunctor_bicat
        psfunctor_psfunctor_bicat_to_fib.
  Proof.
    refine (_ ,, _).
    - exact psfunctor_fib_to_psfunctor_unit.
    - exact psfunctor_fib_to_psfunctor_counit.
  Defined.

  Definition is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat
             (H : is_univalent_2 (fib_slice_bicat C))
    : is_biequivalence_adjoints psfunctor_fib_to_psfunctor_bicat_unit_counit.
  Proof.
    split.
    - use pointwise_adjequiv_to_adjequiv.
      + exact H.
      + intro P.
        use equiv_to_adjequiv.
        exact (psfunctor_fib_to_psfunctor_unit_equiv (pr1 P) (pr2 P)).
    - use pointwise_adjequiv_to_adjequiv.
      + use psfunctor_bicat_is_univalent_2.
        exact univalent_cat_is_univalent_2.
      + intro F.
        use pointwise_adjequiv_to_adjequiv.
        * exact univalent_cat_is_univalent_2.
        * intro x.
          use equiv_to_adjequiv.
          exact (equiv_psfunctor_fib_to_psfunctor_counit_data_ob_data_functor F x).
  Defined.

  Definition is_biequivalence_psfunctor_fib_to_psfunctor_bicat
             (H : is_univalent_2 (fib_slice_bicat C))
    : is_biequivalence psfunctor_fib_to_psfunctor_bicat
    := psfunctor_psfunctor_bicat_to_fib
       ,,
       psfunctor_fib_to_psfunctor_bicat_unit_counit
       ,,
       is_biequivalence_adjoints_psfunctor_fib_to_psfunctor_bicat H.

  Definition grothendieck_construction
             (H : is_univalent_2 (fib_slice_bicat C))
    : biequivalence
        (fib_slice_bicat C)
        (psfunctor_bicat (cat_to_bicat (C^op)) bicat_of_univ_cats)
    := psfunctor_fib_to_psfunctor_bicat
       ,,
       is_biequivalence_psfunctor_fib_to_psfunctor_bicat H.
End GrothendieckConstruction.
