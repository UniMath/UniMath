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

Definition transportf_iso_functors
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x₁ x₂ : C₁}
           (y : C₂)
           (p : x₁ = x₂)
           (i : iso (F x₁) y)
  : pr1 (transportf (λ (x : C₁), iso (F x) y) p i)
    =
    #F (inv_from_iso (idtoiso p)) · i.
Proof.
  induction p ; cbn.
  rewrite functor_id.
  rewrite id_left.
  apply idpath.
Qed.

(**
 1. Esos
 *)
Section EsoIsEssentiallySurjective.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : is_eso F).

  Let im : bicat_of_univ_cats := univalent_image F.
  Let fim : C₁ --> im := functor_full_img F.
  Let π : im --> C₂ := sub_precategory_inclusion _ _.

  Definition eso_is_essentially_surjective_inv2cell
    : invertible_2cell (fim · π) (F · id₁ C₂).
  Proof.
    use nat_iso_to_invertible_2cell.
    use make_nat_iso.
    - use make_nat_trans.
      + exact (λ _, identity _).
      + abstract
          (intro ; intros ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    - intro.
      apply identity_is_iso.
  Defined.

  Definition eso_is_essentially_surjective_lift
    : C₂ --> im
    := is_eso_lift_1
         _
         HF
         (cat_fully_faithful_is_fully_faithful_1cell
            π
            (fully_faithful_sub_precategory_inclusion _ _))
         fim
         (id₁ _)
         eso_is_essentially_surjective_inv2cell.

  Let φ := eso_is_essentially_surjective_lift.

  Definition eso_is_essentially_surjective
    : essentially_surjective F.
  Proof.
    intro x.
    use (factor_through_squash _ _ (pr2 (pr1 φ x))).
    {
      apply ishinh.
    }
    intros q.
    use hinhpr.
    simple refine (_ ,, _).
    - exact (pr1 q).
    - simpl.
      refine (iso_comp (pr2 q) _).
      exact (nat_iso_pointwise_iso
               (invertible_2cell_to_nat_iso
                  _ _
                  (is_eso_lift_1_comm_right
                     _
                     HF
                     (cat_fully_faithful_is_fully_faithful_1cell
                        π
                        (fully_faithful_sub_precategory_inclusion _ _))
                     fim
                     (id₁ _)
                     eso_is_essentially_surjective_inv2cell))
               x).
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

  Section EssentiallySurjectiveLift.
    Context {D₁ D₂ : bicat_of_univ_cats}
            {G : D₁ --> D₂}
            (HG : fully_faithful_1cell G)
            (H₁ : C₁ --> D₁)
            (H₂ : C₂ --> D₂)
            (α : invertible_2cell (H₁ · G) (F · H₂)).

    Let HG' : fully_faithful G
      := cat_fully_faithful_1cell_is_fully_faithful _ HG.
    Let α' : nat_iso (H₁ ∙ G) (F ∙ H₂)
      := invertible_2cell_to_nat_iso _ _ α.

    Local Definition isaprop_ob_fiber
               (y : pr1 C₂)
      : isaprop (∑ (x : pr1 D₁), iso (pr1 G x) (pr1 H₂ y)).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use total2_paths_f.
      - apply (isotoid _ (pr2 D₁)).
        exact (make_iso
                 _
                 (fully_faithful_reflects_iso_proof
                    _ _ _
                    HG'
                    _ _
                    (iso_comp (pr2 φ₁) (iso_inv_from_iso (pr2 φ₂))))).
      - use subtypePath.
        {
          intro.
          apply isaprop_is_iso.
        }
        etrans.
        {
          apply transportf_iso_functors.
        }
        rewrite functor_on_inv_from_iso.
        use iso_inv_on_right.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          cbn.
          rewrite idtoiso_isotoid.
          apply (homotweqinvweq (make_weq _ (HG' _ _)) _).
        }
        rewrite !assoc'.
        rewrite iso_after_iso_inv.
        apply id_right.
    Qed.

    Local Definition iscontr_ob_fiber
               (y : pr1 C₂)
      : iscontr (∑ (x : pr1 D₁), iso (pr1 G x) (pr1 H₂ y)).
    Proof.
      use (factor_through_squash _ _ (HF y)).
      - apply isapropiscontr.
      - intros z.
        use iscontraprop1.
        + exact (isaprop_ob_fiber y).
        + refine (pr1 H₁ (pr1 z) ,, _).
          exact (iso_comp
                   (nat_iso_pointwise_iso α' (pr1 z))
                   (functor_on_iso H₂ (pr2 z))).
    Defined.

    Local Definition isaprop_mor_fiber
               {y₁ y₂ : pr1 C₂}
               (g : y₁ --> y₂)
               {x₁ x₂ : pr1 D₁}
               (i₁ : iso (pr1 G x₁) (pr1 H₂ y₁))
               (i₂ : iso (pr1 G x₂) (pr1 H₂ y₂))
      : isaprop (∑ (f : x₁ --> x₂), i₁ · # (pr1 H₂) g = # (pr1 G) f · i₂).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (invmaponpathsweq (make_weq _ (HG' x₁ x₂))) ; cbn.
      use (cancel_postcomposition_iso i₂).
      exact (!(pr2 φ₁) @ pr2 φ₂).
    Qed.

    Local Definition iscontr_mor_fiber
               {y₁ y₂ : pr1 C₂}
               (g : y₁ --> y₂)
               {x₁ x₂ : pr1 D₁}
               (i₁ : iso (pr1 G x₁) (pr1 H₂ y₁))
               (i₂ : iso (pr1 G x₂) (pr1 H₂ y₂))
      : iscontr (∑ (f : x₁ --> x₂),
                 i₁ · # (pr1 H₂) g
                 =
                 # (pr1 G) f · i₂).
    Proof.
      pose (HG'' := pr1 (fully_faithful_implies_full_and_faithful _ _ _ HG')
                        x₁ x₂
                        (i₁ · #(pr1 H₂) g · inv_from_iso i₂)).
      use (factor_through_squash _ _ HG'').
      - apply isapropiscontr.
      - intro f.
        apply iscontraprop1.
        + exact (isaprop_mor_fiber g i₁ i₂).
        + refine (pr1 f ,, _).
          abstract
            (pose (p := pr2 f) ;
             cbn in p ;
             refine (!_) ;
             refine (maponpaths (λ z, z · _) p @ _) ;
             rewrite !assoc' ;
             rewrite iso_after_iso_inv ;
             rewrite id_right ;
             apply idpath).
    Defined.

    Local Definition mor_fiber_eq
               {y₁ y₂ : pr1 C₂}
               (g : y₁ --> y₂)
               {x₁ x₂ : pr1 D₁}
               (i₁ : iso (pr1 G x₁) (pr1 H₂ y₁))
               (i₂ : iso (pr1 G x₂) (pr1 H₂ y₂))
               (h : x₁ --> x₂)
               (p : i₁ · # (pr1 H₂) g
                    =
                    # (pr1 G) h · i₂)
      : pr11 (iscontr_mor_fiber g i₁ i₂) = h.
    Proof.
      refine (!_).
      exact (maponpaths pr1 (pr2 (iscontr_mor_fiber g i₁ i₂) (h ,, p))).
    Qed.

    Local Definition essentially_surjective_is_eso_lift_data
      : functor_data (pr1 C₂) (pr1 D₁).
    Proof.
      use make_functor_data.
      - exact (λ y, pr11 (iscontr_ob_fiber y)).
      - intros y₁ y₂ g.
        exact (pr11 (iscontr_mor_fiber
                       g
                       (pr21 (iscontr_ob_fiber y₁))
                       (pr21 (iscontr_ob_fiber y₂)))).
    Defined.

    Local Definition essentially_surjective_is_eso_lift_is_functor
      : is_functor essentially_surjective_is_eso_lift_data.
    Proof.
      split.
      - intro y ; cbn.
        use mor_fiber_eq.
        rewrite (functor_id H₂), (functor_id G).
        rewrite id_left, id_right.
        apply idpath.
      - intros y₁ y₂ y₃ g₁ g₂ ; cbn.
        use mor_fiber_eq.
        rewrite (functor_comp H₂).
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr21 (iscontr_mor_fiber
                         g₁
                         (pr21 (iscontr_ob_fiber y₁))
                         (pr21 (iscontr_ob_fiber y₂)))).
        }
        rewrite (functor_comp G).
        rewrite !assoc'.
        apply maponpaths.
        exact (pr21 (iscontr_mor_fiber
                       g₂
                       (pr21 (iscontr_ob_fiber y₂))
                       (pr21 (iscontr_ob_fiber y₃)))).
    Qed.

    Definition essentially_surjective_is_eso_lift
      : C₂ --> D₁.
    Proof.
      use make_functor.
      - exact essentially_surjective_is_eso_lift_data.
      - exact essentially_surjective_is_eso_lift_is_functor.
    Defined.

    Local Definition essentially_surjective_is_eso_lift_left_nat_trans_data
      : nat_trans_data
          (F ∙ essentially_surjective_is_eso_lift)
          (pr1 H₁)
      := λ x,
         fully_faithful_inv_hom
           HG'
           _ _
           (pr21 (iscontr_ob_fiber (pr1 F x))
            · inv_from_iso (nat_iso_pointwise_iso α' x)).

    Local Definition essentially_surjective_is_eso_lift_left_is_nat_trans
      : is_nat_trans
          _ _
          essentially_surjective_is_eso_lift_left_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      use (invmaponpathsweq (make_weq _ (HG' _ _))).
      cbn.
      refine (functor_comp _ _ _@ _ @ !(functor_comp _ _ _)).
      etrans.
      {
        apply maponpaths.
        apply (homotweqinvweq (make_weq _ (HG' _ _))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (homotweqinvweq (make_weq _ (HG' _ _))).
      }
      unfold precomp_with.
      rewrite !id_right.
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr21 (iscontr_mor_fiber
                         (#(pr1 F) f)
                         (pr21 (iscontr_ob_fiber (pr1 F x)))
                         (pr21 (iscontr_ob_fiber (pr1 F y)))))).
      }
      rewrite !assoc'.
      apply maponpaths.
      apply (nat_trans_ax (α^-1)).
    Qed.

    Definition essentially_surjective_is_eso_lift_left_nat_trans
      : F ∙ essentially_surjective_is_eso_lift ⟹ pr1 H₁.
    Proof.
      use make_nat_trans.
      - exact essentially_surjective_is_eso_lift_left_nat_trans_data.
      - exact essentially_surjective_is_eso_lift_left_is_nat_trans.
    Defined.

    Definition essentially_surjective_is_eso_lift_left
      : invertible_2cell
          (F · essentially_surjective_is_eso_lift)
          H₁.
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact essentially_surjective_is_eso_lift_left_nat_trans.
      - intro.
        use (fully_faithful_reflects_iso_proof _ _ _ HG' _ _ (make_iso _ _)).
        use is_iso_comp_of_is_isos.
        + apply iso_is_iso.
        + apply is_iso_inv_from_iso.
    Defined.

    Definition essentially_surjective_is_eso_lift_right_nat_trans
      : essentially_surjective_is_eso_lift ∙ G ⟹ pr1 H₂.
    Proof.
      use make_nat_trans.
      - exact (λ y, pr21 (iscontr_ob_fiber y)).
      - abstract
          (intros y₁ y₂ f ; cbn ;
           exact (!(pr21 (iscontr_mor_fiber
                            f
                            (pr21 (iscontr_ob_fiber y₁))
                            (pr21 (iscontr_ob_fiber y₂)))))).
    Defined.

    Definition essentially_surjective_is_eso_lift_right
      : invertible_2cell
          (essentially_surjective_is_eso_lift · G)
          H₂.
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact essentially_surjective_is_eso_lift_right_nat_trans.
      - intro.
        apply iso_is_iso.
    Defined.

    Definition essentially_surjective_is_eso_lift_eq
      : (essentially_surjective_is_eso_lift_left ▹ G) • α
        =
        rassociator _ _ _
        • (F ◃ essentially_surjective_is_eso_lift_right).
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      cbn.
      refine (_ @ !(id_left _)).
      etrans.
      {
        apply maponpaths_2.
        exact (homotweqinvweq (make_weq _ (HG' _ _)) _).
      }
      unfold precomp_with.
      rewrite id_right.
      rewrite assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      exact (nat_trans_eq_pointwise (vcomp_linv α) x).
    Qed.
  End EssentiallySurjectiveLift.

  Definition essentially_surjective_is_eso_essentially_surjective
    : is_eso_essentially_surjective F.
  Proof.
    intros D₁ D₂ G HG H₁ H₂ α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (essentially_surjective_is_eso_lift HG H₁ H₂ α).
    - exact (essentially_surjective_is_eso_lift_left HG H₁ H₂ α).
    - exact (essentially_surjective_is_eso_lift_right HG H₁ H₂ α).
    - exact (essentially_surjective_is_eso_lift_eq HG H₁ H₂ α).
  Defined.

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
