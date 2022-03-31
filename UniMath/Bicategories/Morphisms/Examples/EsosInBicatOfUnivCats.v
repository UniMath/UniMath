(**
 Morphisms in the bicat of univalent categories

 Contents:
 1. Esos
 2. (eso, ff)-factorization
 3. Esos are closed under pullback
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Eso.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.

Local Open Scope cat.

(**
 1. Esos
 *)
Section EsoIsEssentiallySurjective.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : is_eso F).

  Section InImage.
    Context (x : pr1 C₂).

    Definition eso_is_essentially_surjective_preimage
      : pr1 C₁.
    Proof.
    Admitted.

    Definition eso_is_essentially_surjective_iso
      : iso (pr1 F eso_is_essentially_surjective_preimage) x.
    Proof.
    Admitted.
  End InImage.

  Definition eso_is_essentially_surjective
    : essentially_surjective F.
  Proof.
    intro x.
    use hinhpr.
    simple refine (_ ,, _).
    - apply eso_is_essentially_surjective_preimage.
      exact x.
    - apply eso_is_essentially_surjective_iso.
  Defined.
End EsoIsEssentiallySurjective.

Section EssentiallySurjectiveIsEso.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : essentially_surjective F).

  Section EssentiallySurjectiveEsoFull.
    Context {D₁ D₂ : bicat_of_univ_cats}
            {G : D₁ --> D₂}
            (HG : fully_faithful_1cell G)
            {H₁ H₂ : C₂ --> D₁}
            (n₁ : F · H₁ ==> F · H₂)
            (n₂ : H₁ · G ==> H₂ · G)
            (p : (n₁ ▹ G) • rassociator F H₂ G
                 =
                 rassociator F H₁ G • (F ◃ n₂)).

    Definition essentially_surjective_is_eso_lift_2_data
      : nat_trans_data (pr1 H₁) (pr1 H₂)
      := λ x, invmap
                (make_weq
                   _
                   (cat_fully_faithful_1cell_is_fully_faithful
                      _
                      HG
                      (pr1 H₁ x)
                      (pr1 H₂ x)))
                (pr1 n₂ x).

    Definition essentially_surjective_is_eso_lift_2_is_nat_trans
      : is_nat_trans _ _ essentially_surjective_is_eso_lift_2_data.
    Proof.
      intros x y f.
      unfold essentially_surjective_is_eso_lift_2_data.
      pose (H := homotinvweqweq
                   (make_weq
                      _
                      (cat_fully_faithful_1cell_is_fully_faithful
                         _
                         HG
                         (pr1 H₁ x)
                         (pr1 H₂ y)))).
      refine (!(H _) @ _ @ H _) ; clear H.
      apply maponpaths.
      cbn.
      rewrite !functor_comp.
      etrans.
      {
        apply maponpaths.
        apply (homotweqinvweq
                 (make_weq
                    _
                    (cat_fully_faithful_1cell_is_fully_faithful
                       _
                       HG
                       (pr1 H₁ y)
                       (pr1 H₂ y)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (homotweqinvweq
                 (make_weq
                    _
                    (cat_fully_faithful_1cell_is_fully_faithful
                       _
                       HG
                       (pr1 H₁ x)
                       (pr1 H₂ x)))).
      }
      exact (!(nat_trans_ax n₂ _ _ f)).
    Qed.

    Definition essentially_surjective_is_eso_lift_2
      : H₁ ==> H₂.
    Proof.
      use make_nat_trans.
      - exact essentially_surjective_is_eso_lift_2_data.
      - exact essentially_surjective_is_eso_lift_2_is_nat_trans.
    Defined.

    Definition essentially_surjective_is_eso_lift_2_left
      : F ◃ essentially_surjective_is_eso_lift_2 = n₁.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      cbn.
      unfold essentially_surjective_is_eso_lift_2_data.
      pose (H := homotinvweqweq
                   (make_weq
                      _
                      (cat_fully_faithful_1cell_is_fully_faithful
                         _
                         HG
                         (pr1 H₁ (pr1 F x))
                         (pr1 H₂ (pr1 F x))))).
      refine (!(H _) @ _ @ H _) ; clear H.
      apply maponpaths.
      cbn.
      etrans.
      {
        apply (homotweqinvweq
                 (make_weq
                    _
                    (cat_fully_faithful_1cell_is_fully_faithful
                       _
                       HG
                       (pr1 H₁ (pr1 F x))
                       (pr1 H₂ (pr1 F x))))).
      }
      refine (_ @ !(nat_trans_eq_pointwise p x) @ _) ; cbn.
      - rewrite id_left.
        apply idpath.
      - rewrite id_right.
        apply idpath.
    Qed.

    Definition essentially_surjective_is_eso_lift_2_right
      : essentially_surjective_is_eso_lift_2 ▹ G = n₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      cbn.
      unfold essentially_surjective_is_eso_lift_2_data.
      apply (homotweqinvweq
                 (make_weq
                    _
                    (cat_fully_faithful_1cell_is_fully_faithful
                       _
                       HG
                       _ _))).
    Qed.
  End EssentiallySurjectiveEsoFull.

  Definition essentially_surjective_is_eso_full
    : is_eso_full F.
  Proof.
    intros D₁ D₂ G HG H₁ H₂ n₁ n₂ p.
    simple refine (_ ,, _ ,, _).
    - exact (essentially_surjective_is_eso_lift_2 HG n₂).
    - exact (essentially_surjective_is_eso_lift_2_left HG _ _ p).
    - apply essentially_surjective_is_eso_lift_2_right.
  Defined.

  Definition essentially_surjective_is_eso_faithful
    : is_eso_faithful F.
  Proof.
    intros D₁ D₂ G HG H₁ H₂ n₁ n₂ p₁ p₂.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro y.
    use (factor_through_squash _ _ (HF y)).
    - apply homset_property.
    - intro xx.
      induction xx as [ x i ].
      use (cancel_precomposition_iso (functor_on_iso H₁ i)).
      cbn.
      rewrite !nat_trans_ax.
      apply maponpaths_2.
      exact (nat_trans_eq_pointwise p₁ x).
  Qed.

  Definition essentially_surjective_is_eso_essentially_surjective
    : is_eso_essentially_surjective F.
  Proof.
    intros D₁ D₂ G HG H₁ H₂ α.
    simple refine (_ ,, _).
    - cbn.
  Admitted.

  Definition essentially_surjective_is_eso
    : is_eso F.
  Proof.
    use make_is_eso.
    - exact univalent_cat_is_univalent_2_1.
    - exact essentially_surjective_is_eso_full.
    - exact essentially_surjective_is_eso_faithful.
    - exact essentially_surjective_is_eso_essentially_surjective.
  Defined.
End EssentiallySurjectiveIsEso.

Definition eso_weq_essentially_surjective
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : is_eso F ≃ essentially_surjective F.
Proof.
  use weqimplimpl.
  - exact eso_is_essentially_surjective.
  - exact essentially_surjective_is_eso.
  - apply isaprop_is_eso.
    exact univalent_cat_is_univalent_2_1.
  - apply isaprop_essentially_surjective.
Defined.

(**
 2. (eso, ff)-factorization
 *)
Definition eso_ff_factorization_bicat_of_univ_cats
  : eso_ff_factorization bicat_of_univ_cats.
Proof.
  intros C₁ C₂ F.
  refine (univalent_image F ,, sub_precategory_inclusion _ _ ,, functor_full_img _ ,, _).
  simple refine (_ ,, _ ,, _).
  - use cat_fully_faithful_is_fully_faithful_1cell.
    apply fully_faithful_sub_precategory_inclusion.
  - use essentially_surjective_is_eso.
    apply functor_full_img_essentially_surjective.
  - use nat_iso_to_invertible_2cell.
    exact (full_image_inclusion_commute_nat_iso F).
Defined.

(**
 3. Esos are closed under pullback
 *)
Definition is_eso_closed_under_pb_bicat_of_univ_cats
  : is_eso_closed_under_pb (_ ,, has_pb_bicat_of_univ_cats).
Proof.
  intros C₁ C₂ C₃ F HF G.
  cbn.
  apply essentially_surjective_is_eso.
  apply iso_comma_essentially_surjective.
  apply eso_is_essentially_surjective.
  exact HF.
Defined.
