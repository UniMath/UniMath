(************************************************************************

 Grothendieck construction: fibrations to pseudofunctors

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

 In this file, we construct the first part of this biequivalence (a
 pseudofunctor from fibrations to pseudofunctors). This construction
 mainly recollects statements that are already present in UniMath.

 There are a couple of ideas behind this formalization. First of all,
 for the Grothendieck construction, we are only interested in a rather
 particular class of pseudofunctors, namely those pseudofunctors for
 which the domain is a discrete bicategory (i.e., a category). This
 allows us to simplify some of the coherences of pseudofunctors, which
 is done in the file `PseudoTransformationIntoCat.v`. Second of all, we
 explicitly use the notion of indexed categories (see the directory
 `IndexedCategories` in `CategoryTheory`) for this construction, because
 this allows us to formulate the fundamental constructions purely in the
 language of category theory and without mentioning bicategories.

 Contents
 1. Preservation of the identity
 2. Preservation of composition
 3. The data
 4. The laws
 5. Pseudofunctor from fibrations to pseudofunctors

 ************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
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
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.Core.Examples.FibSlice.
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

(**
 1. Preservation of the identity
 *)
Definition psfunctor_id_fib_to_psfunctor_bicat_data
           {C : category}
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
           {C : category}
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
           {C : category}
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
 2. Preservation of composition
 *)
Definition psfunctor_comp_fib_to_psfunctor_bicat_data
           {C : category}
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
            {C : category}
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
           {C : category}
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
   3. The data
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
   4. The laws
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
   5. Pseudofunctor from fibrations to pseudofunctors
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
End GrothendieckConstruction.
