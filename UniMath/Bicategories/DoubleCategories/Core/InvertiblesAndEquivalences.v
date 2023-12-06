(**********************************************************************************

 Equivalences and invertible 2-cells of double categories

 In this file, we give constructors for adjoints equivalences and invertible
 2-cells in the bicategory of double categories.

 If we have a double transformation, then to show it is an invertible 2-cells, it
 suffices to prove that underlying vertical and horizontal transformations are
 pointwise inertible.

 To prove that a lax double functor `F` is an equivalence, it suffices to prove the
 following:
 - `F` is strong (it preserves the horizontal identity and composition up to
   isomorphism).
 - `F` is an adjoint equivalence on the level of 2-sided displayed categories. This
   means that the underlying vertical and horizontal functors are equivalences.
 This is proven in [left_adjoint_equivalence_lax_double_functor]. Note that we do
 not have to show that the inverse is a double functor or that the involved natural
 transformations are double transformations.

 We also show that these conditions are necessary. For the invertible 2-cells, this
 follows from the fact that the first projection of an invertible 2-cell in the
 total bicategory is also invertible. For adjoint equivalence, we need the analogous
 statement, but we also need to show that adjoint equivalences are strong double
 functors. For that, we use induction on adjoint equivalences, and the fact that
 the identity functor is a strong double functor.

 Contents
 1. Invertible 2-cells
 2. Adjoint equivalences

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfTwoSidedDispCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleTransformation.
Require Import UniMath.Bicategories.DoubleCategories.Core.BicatOfDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Invertible 2-cells *)
Section Invertibles.
  Context {C₁ C₂ : univalent_double_cat}
          {F G : lax_double_functor C₁ C₂}
          (τ : double_transformation F G)
          (Hτ : is_invertible_2cell (pr111 τ)).

  Definition is_invertible_2cell_double_transformation_help
    : is_invertible_2cell (pr11 τ).
  Proof.
    use is_invertible_disp_to_total.
    simple refine (_ ,, _).
    - (* 2-sided displayed categories *)
      exact Hτ.
    - use (pair_is_disp_invertible_2cell _ _ (_ ,, _) (pr211 τ)).
      split.
      + (* horizontal identities *)
        apply is_disp_invertible_2cell_hor_id.
      + (* horizontal compositions *)
        apply is_disp_invertible_2cell_hor_comp.
  Qed.

  Definition is_invertible_2cell_double_transformation
    : is_invertible_2cell τ.
  Proof.
    use bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
    use is_invertible_disp_to_total.
    simple refine (_ ,, _).
    - exact is_invertible_2cell_double_transformation_help.
    - use (pair_is_disp_invertible_2cell _ _ (_ ,, _) (pr21 τ)).
      split.
      + (* left unitors *)
        apply disp_cell_unit_bicat_is_disp_invertible_2cell.
      + use (pair_is_disp_invertible_2cell _ _ (_ ,, _) (pr221 τ)).
        refine (_ ,, _).
        * (* right unitors *)
          apply disp_cell_unit_bicat_is_disp_invertible_2cell.
        * (* associators *)
          apply disp_cell_unit_bicat_is_disp_invertible_2cell.
  Qed.
End Invertibles.

Definition invertible_double_nat_trans_weq
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : double_transformation F G)
  : is_invertible_2cell τ ≃ is_invertible_2cell (pr111 τ).
Proof.
  use weqimplimpl.
  - intros Hτ.
    exact (is_invertible_total_to_base
             _ _
             (is_invertible_total_to_base
                _ _
                (is_invertible_total_to_base _ _ Hτ))).
  - intros Hτ.
    use is_invertible_2cell_double_transformation.
    exact Hτ.
  - apply isaprop_is_invertible_2cell.
  - apply isaprop_is_invertible_2cell.
Defined.

Section InvertiblesUnfolded.
  Context {C₁ C₂ : univalent_double_cat}
          {F G : lax_double_functor C₁ C₂}
          (τ : double_transformation F G)
          (Hτ : ∏ (x : C₁), is_z_isomorphism (τ x))
          (Hττ : ∏ (x y : C₁)
                   (f : x -->h y),
                 is_iso_twosided_disp
                   (Hτ x) (Hτ y)
                   (double_transformation_hor_mor τ f)).

  Definition is_invertible_2cell_double_transformation_unfolded
    : is_invertible_2cell τ.
  Proof.
    use is_invertible_2cell_double_transformation.
    use is_invertible_2cell_bicat_twosided_disp_cat.
    - exact Hτ.
    - exact Hττ.
  Qed.
End InvertiblesUnfolded.

(** * 2. Adjoint equivalences *)
Section Equivalences.
  Context {C₁ C₂ : univalent_double_cat}
          (F : lax_double_functor C₁ C₂)
          (HF : is_strong_double_functor F)
          (* `F` is an adjoint equivalence of 2-sided displayed categories *)
          (HF' : left_adjoint_equivalence (pr111 F)).

  Definition left_adjoint_equivalence_lax_double_functor_help
    : left_adjoint_equivalence (pr11 F).
  Proof.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    - (* 2-sided displayed categories *)
      exact HF'.
    - use (pair_left_adjoint_equivalence _ _ (_ ,, _) (pr211 F)).
      split.
      + (* horizontal identities *)
        use disp_left_adjequiv_hor_id.
        exact (is_iso_strong_double_functor_id_h HF).
      + (* horizontal compositions *)
        use disp_left_adjequiv_hor_comp.
        exact (λ x y z h k, is_iso_strong_double_functor_comp_h HF h k).
  Qed.

  Definition left_adjoint_equivalence_lax_double_functor
    : left_adjoint_equivalence F.
  Proof.
    use bicat_left_adjoint_equivalence_to_fullsub_left_adjoint_equivalence.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    - exact left_adjoint_equivalence_lax_double_functor_help.
    - use (pair_left_adjoint_equivalence _ _ (_ ,, _) (pr21 F)).
      split.
      + (* left unitors *)
        apply is_disp_left_adjoint_equivalence_disp_bicat_lunitor.
      + use (pair_left_adjoint_equivalence _ _ (_ ,, _) (pr221 F)).
        split.
        * (* right unitors *)
          apply is_disp_left_adjoint_equivalence_disp_bicat_runitor.
        * (* associators *)
          apply is_disp_left_adjoint_equivalence_disp_bicat_lassociator.
  Qed.
End Equivalences.

Section EquivalencesUnfolded.
  Context {C₁ C₂ : univalent_double_cat}
          (F : lax_double_functor C₁ C₂)
          (HF : is_strong_double_functor F)
          (R : C₂ ⟶ C₁)
          (RR : twosided_disp_functor R R (hor_mor C₂) (hor_mor C₁))
          (η : functor_identity _ ⟹ F ∙ R)
          (Hη : is_nat_z_iso η)
          (ηη : twosided_disp_nat_trans
                  η η
                  (twosided_disp_functor_identity _)
                  (comp_twosided_disp_functor_data
                     (lax_double_functor_hor_mor F)
                     RR))
          (Hηη : ∏ (x y : C₁)
                   (f : x -->h y),
                 is_iso_twosided_disp (Hη x) (Hη y) (ηη x y f))
          (ε : R ∙ F ⟹ functor_identity _)
          (Hε : is_nat_z_iso ε)
          (εε : twosided_disp_nat_trans
                  ε ε
                  (comp_twosided_disp_functor_data
                     RR
                     (lax_double_functor_hor_mor F))
                  (twosided_disp_functor_identity _))
          (Hεε : ∏ (x y : C₂)
                   (f : x -->h y),
                 is_iso_twosided_disp (Hε x) (Hε y) (εε x y f)).

  Definition left_adjoint_equivalence_lax_double_functor_base
    : left_adjoint_equivalence (pr111 F).
  Proof.
    use equiv_to_adjequiv.
    simple refine (((R ,, RR) ,, (η ,, ηη) ,, (ε ,, εε)) ,, _ ,, _).
    - use is_invertible_2cell_bicat_twosided_disp_cat ; cbn.
      + exact Hη.
      + exact Hηη.
    - use is_invertible_2cell_bicat_twosided_disp_cat ; cbn.
      + exact Hε.
      + exact Hεε.
  Qed.

  Definition left_adjoint_equivalence_lax_double_functor_unfolded
    : left_adjoint_equivalence F.
  Proof.
    use left_adjoint_equivalence_lax_double_functor.
    - exact HF.
    - exact left_adjoint_equivalence_lax_double_functor_base.
  Qed.
End EquivalencesUnfolded.

Definition left_adjoint_equivalence_to_strong_help
           {C₁ C₂ : univalent_double_cat}
           (F : adjoint_equivalence C₁ C₂)
  : is_strong_double_functor (pr1 F).
Proof.
  revert C₁ C₂ F.
  use J_2_0.
  - apply is_univalent_2_bicat_of_double_cats.
  - intro C.
    apply is_strong_double_functor_id.
Defined.

Section FromEquivalence.
  Context {C₁ C₂ : univalent_double_cat}
          (F : lax_double_functor C₁ C₂)
          (HF : left_adjoint_equivalence F).

  Let HF₁ : left_adjoint_equivalence (pr1 F)
    := pr1 (left_adjoint_equivalence_total_disp_weq _ _ HF).

  Let HF₂ : left_adjoint_equivalence (pr11 F)
    := pr1 (left_adjoint_equivalence_total_disp_weq _ _ HF₁).

  Definition left_adjoint_equivalence_to_strong
    : is_strong_double_functor F
    := left_adjoint_equivalence_to_strong_help (F ,, HF).

  Definition left_adjoint_equivalence_to_twosided_equiv
    : left_adjoint_equivalence (pr111 F).
  Proof.
    exact (pr1 (left_adjoint_equivalence_total_disp_weq _ _ HF₂)).
  Defined.
End FromEquivalence.

Definition left_adjoint_equivalence_lax_double_functor_weq
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : left_adjoint_equivalence F
    ≃
    (is_strong_double_functor F × left_adjoint_equivalence (pr111 F)).
Proof.
  use weqimplimpl.
  - intros HF.
    split.
    + exact (left_adjoint_equivalence_to_strong F HF).
    + exact (left_adjoint_equivalence_to_twosided_equiv F HF).
  - intros HF.
    use left_adjoint_equivalence_lax_double_functor.
    + exact (pr1 HF).
    + exact (pr2 HF).
  - apply isaprop_left_adjoint_equivalence.
    apply is_univalent_2_bicat_of_double_cats.
  - apply isapropdirprod.
    + apply isaprop_is_strong_double_functor.
    + apply isaprop_left_adjoint_equivalence.
      exact is_univalent_2_1_bicat_twosided_disp_cat.
Defined.
