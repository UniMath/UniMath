(****************************************************************

 Iso comma categories

 Given functors `F : C₁ ⟶ C₃` and `G : C₂ ⟶ C₃`.
 Then the iso-comma category of `F` and `G` is defined as follows:
 - Objects: pairs `(x, y) : C₁ × C₂` with an iso  `F x --> G y`
 - Morphisms: morphisms from `(x₁, y₁, i₁)` to `(x₂, y₂, i₂)`
              consists of maps `f : x₁ --> x₂` and `g : y₁ --> y₂`
              such that that the following square commutes

                     F x₁   -->     F x₂
                      |              |
                      |              |
                      v              v
                     G y₁   -->     G y₂

 In this file, we define the iso-comma category using displayed
 category. We also prove that it's univalent, and we define the
 necessary projection functors and transformations.

 We also show that the iso-comma category satisfies the universal
 mapping property of a pullback.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Section IsoCommaCategory.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  (** Definition of iso comma categories via displayed categories *)
  Definition iso_comma_disp_cat_ob_mor
    : disp_cat_ob_mor (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, iso (F (pr1 x)) (G (pr2 x))).
    - exact (λ x y i₁ i₂ f, #F (pr1 f) · i₂ = i₁ · #G (pr2 f)).
  Defined.

  Definition iso_comma_disp_cat_id_comp
    : disp_cat_id_comp _ iso_comma_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - intros x i ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - cbn ; intros x y z f g i₁ i₂ i₃ p q.
      rewrite !functor_comp.
      rewrite !assoc'.
      rewrite q.
      rewrite !assoc.
      rewrite p.
      apply idpath.
  Qed.

  Definition iso_comma_disp_cat_data
    : disp_cat_data (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact iso_comma_disp_cat_ob_mor.
    - exact iso_comma_disp_cat_id_comp.
  Defined.

  Definition iso_comma_disp_cat_axioms
    : disp_cat_axioms _ iso_comma_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition iso_comma_disp_cat
    : disp_cat (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact iso_comma_disp_cat_data.
    - exact iso_comma_disp_cat_axioms.
  Defined.

  Definition iso_comma
    : category
    := total_category iso_comma_disp_cat.

  Definition is_pregroupoid_iso_comma
             (HC₁ : is_pregroupoid C₁)
             (HC₂ : is_pregroupoid C₂)
    : is_pregroupoid iso_comma.
  Proof.
    intros x y f.
    use is_iso_qinv.
    - simple refine ((_ ,, _) ,, _).
      + exact (inv_from_iso (make_iso _ (HC₁ _ _ (pr11 f)))).
      + exact (inv_from_iso (make_iso _ (HC₂ _ _ (pr21 f)))).
      + abstract
          (cbn ;
           rewrite !functor_on_inv_from_iso ;
           use iso_inv_on_left ;
           rewrite assoc' ;
           refine (!_) ;
           use iso_inv_on_right ;
           cbn ;
           refine (!_) ;
           apply (pr2 f)).
    - split.
      + abstract
          (use subtypePath ;
           [ intro ; apply homset_property | ] ;
           use pathsdirprod ;
           cbn ;
           [ apply (iso_inv_after_iso (make_iso _ (HC₁ _ _ (pr11 f))))
           | apply (iso_inv_after_iso (make_iso _ (HC₂ _ _ (pr21 f)))) ]).
      + abstract
          (use subtypePath ;
           [ intro ; apply homset_property | ] ;
           use pathsdirprod ;
           cbn ;
           [ apply (iso_after_iso_inv (make_iso _ (HC₁ _ _ (pr11 f))))
           | apply (iso_after_iso_inv (make_iso _ (HC₂ _ _ (pr21 f)))) ]).
  Defined.

  (** Univalence of the iso-comma category *)
  Definition is_univalent_disp_iso_comma_disp_cat
             (HC₃ : is_univalent C₃)
    : is_univalent_disp iso_comma_disp_cat.
  Proof.
    intros x y p i₁ i₂.
    induction p.
    use isweqimplimpl.
    - intros p.
      pose (pr1 p) as m.
      cbn in m.
      rewrite !functor_id in m.
      rewrite id_left, id_right in m.
      use subtypePath.
      {
        intro ; apply isaprop_is_iso.
      }
      exact (!m).
    - apply isaset_iso.
      apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_iso_comma
             (HC₁ : is_univalent C₁)
             (HC₂ : is_univalent C₂)
             (HC₃ : is_univalent C₃)
    : is_univalent iso_comma.
  Proof.
    use is_univalent_total_category.
    - apply is_unvialent_category_binproduct.
      + exact HC₁.
      + exact HC₂.
    - exact (is_univalent_disp_iso_comma_disp_cat HC₃).
  Defined.

  (** Projection functors *)
  Definition iso_comma_pr1
    : iso_comma ⟶ C₁
    := pr1_category iso_comma_disp_cat ∙ pr1_functor C₁ C₂.

  Definition iso_comma_pr2
    : iso_comma ⟶ C₂
    := pr1_category iso_comma_disp_cat ∙ pr2_functor C₁ C₂.

  (** Natural isomorphism witnessing the commutation *)
  Definition iso_comma_commute_nat_trans_data
    : nat_trans_data (iso_comma_pr1 ∙ F) (iso_comma_pr2 ∙ G).
  Proof.
    intros x ; cbn in x.
    exact (pr2 x).
  Defined.

  Definition iso_comma_commute_is_nat_trans
    : is_nat_trans _ _ iso_comma_commute_nat_trans_data.
  Proof.
    intros x y f ; unfold iso_comma_commute_nat_trans_data ; cbn ; cbn in f.
    exact (pr2 f).
  Qed.

  Definition iso_comma_commute_nat_trans
    : iso_comma_pr1 ∙ F ⟹ iso_comma_pr2 ∙ G.
  Proof.
    use make_nat_trans.
    - exact iso_comma_commute_nat_trans_data.
    - exact iso_comma_commute_is_nat_trans.
  Defined.

  Definition iso_comma_commute
    : nat_iso
        (iso_comma_pr1 ∙ F)
        (iso_comma_pr2 ∙ G).
  Proof.
    use make_nat_iso.
    - exact iso_comma_commute_nat_trans.
    - intros x.
      apply iso_is_iso.
  Defined.

  (**
     Mapping property of iso-comma category

     We need to check three mapping properties:
     - The first one gives the existence of a functor
     - The second one gives the existence of a natural transformation
     - The third one can be used to show that two natural transformations
       are equal
   *)
  Section UniversalMappingProperty.
    Context {D : category}
            (P : D ⟶ C₁)
            (Q : D ⟶ C₂)
            (η : nat_iso (P ∙ F) (Q ∙ G)).

    (** The functor witnessing the universal property *)
    Definition iso_comma_ump1_data
      : functor_data D iso_comma.
    Proof.
      use make_functor_data.
      - exact (λ d, (P d ,, Q d) ,, nat_iso_pointwise_iso η d).
      - exact (λ d₁ d₂ f, (#P f ,, #Q f) ,, nat_trans_ax η _ _ f).
    Defined.

    Definition iso_comma_ump1_is_functor
      : is_functor iso_comma_ump1_data.
    Proof.
      split.
      - intro x ; cbn.
        use subtypePath.
        {
          intro ; apply homset_property.
        }
        cbn.
        rewrite !functor_id.
        apply idpath.
      - intros x y z f g ; cbn.
        use subtypePath.
        {
          intro ; apply homset_property.
        }
        cbn.
        rewrite !functor_comp.
        apply idpath.
    Qed.

    Definition iso_comma_ump1
      : D ⟶ iso_comma.
    Proof.
      use make_functor.
      - exact iso_comma_ump1_data.
      - exact iso_comma_ump1_is_functor.
    Defined.

    (** The computation rules *)
    Definition iso_comma_ump1_pr1_nat_trans_data
      : nat_trans_data (iso_comma_ump1 ∙ iso_comma_pr1) P
      := λ x, identity _.

    Definition iso_comma_ump1_pr1_is_nat_trans
      : is_nat_trans _ _ iso_comma_ump1_pr1_nat_trans_data.
    Proof.
      intros x y f ; cbn ; unfold iso_comma_ump1_pr1_nat_trans_data.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition iso_comma_ump1_pr1_nat_trans
      : iso_comma_ump1 ∙ iso_comma_pr1 ⟹ P.
    Proof.
      use make_nat_trans.
      - exact iso_comma_ump1_pr1_nat_trans_data.
      - exact iso_comma_ump1_pr1_is_nat_trans.
    Defined.

    (** Computation rule for first projection *)
    Definition iso_comma_ump1_pr1
      : nat_iso (iso_comma_ump1 ∙ iso_comma_pr1) P.
    Proof.
      use make_nat_iso.
      - exact iso_comma_ump1_pr1_nat_trans.
      - intro.
        apply identity_is_iso.
    Defined.

    Definition iso_comma_ump1_pr2_nat_trans_data
      : nat_trans_data (iso_comma_ump1 ∙ iso_comma_pr2) Q
      := λ x, identity _.

    Definition iso_comma_ump1_pr2_is_nat_trans
      : is_nat_trans _ _ iso_comma_ump1_pr2_nat_trans_data.
    Proof.
      intros x y f ; cbn ; unfold iso_comma_ump1_pr2_nat_trans_data.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition iso_comma_ump1_pr2_nat_trans
      : iso_comma_ump1 ∙ iso_comma_pr2 ⟹ Q.
    Proof.
      use make_nat_trans.
      - exact iso_comma_ump1_pr2_nat_trans_data.
      - exact iso_comma_ump1_pr2_is_nat_trans.
    Defined.

    (** Computation rule for second projection *)
    Definition iso_comma_ump1_pr2
      : nat_iso (iso_comma_ump1 ∙ iso_comma_pr2) Q.
    Proof.
      use make_nat_iso.
      - exact iso_comma_ump1_pr2_nat_trans.
      - intro.
        apply identity_is_iso.
    Defined.

    (** Computation rule for natural iso *)
    Definition iso_comma_ump1_commute
      : pre_whisker iso_comma_ump1 iso_comma_commute
        =
        nat_trans_comp
          _ _ _
          (nat_trans_functor_assoc_inv _ _ _)
          (nat_trans_comp
             _ _ _
             (post_whisker iso_comma_ump1_pr1 F)
             (nat_trans_comp
                _ _ _
                η
                (nat_trans_comp
                   _ _ _
                   (post_whisker (nat_iso_inv iso_comma_ump1_pr2) G)
                   (nat_trans_functor_assoc _ _ _)))).
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro ; cbn ; unfold iso_comma_ump1_pr1_nat_trans_data.
      rewrite (functor_id F), (functor_id G).
      rewrite !id_left.
      rewrite id_right.
      apply idpath.
    Qed.

    (** Now we look at the second universal mapping property *)
    Context (Φ₁ Φ₂ : D ⟶ iso_comma)
            (τ₁ : Φ₁ ∙ iso_comma_pr1 ⟹ Φ₂ ∙ iso_comma_pr1)
            (τ₂ : Φ₁ ∙ iso_comma_pr2 ⟹ Φ₂ ∙ iso_comma_pr2)
            (p : ∏ (x : D),
                 pr12 (Φ₁ x) · #G (τ₂ x)
                 =
                 #F (τ₁ x) · pr12 (Φ₂ x)).

    Definition iso_comma_ump2_nat_trans_data
      : nat_trans_data Φ₁ Φ₂.
    Proof.
      intro x.
      simple refine ((_ ,, _) ,, _) ; cbn.
      - exact (τ₁ x).
      - exact (τ₂ x).
      - abstract
          (exact (!(p x))).
    Defined.

    Definition iso_comma_ump2_is_nat_trans
      : is_nat_trans _ _ iso_comma_ump2_nat_trans_data.
    Proof.
      intros x y f.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      use pathsdirprod.
      - exact (nat_trans_ax τ₁ _ _ f).
      - exact (nat_trans_ax τ₂ _ _ f).
    Qed.

    Definition iso_comma_ump2
      : Φ₁ ⟹ Φ₂.
    Proof.
      use make_nat_trans.
      - exact iso_comma_ump2_nat_trans_data.
      - exact iso_comma_ump2_is_nat_trans.
    Defined.

    (** The computation rules *)
    Definition iso_comma_ump2_pr1
      : post_whisker iso_comma_ump2 iso_comma_pr1 = τ₁.
    Proof.
      use nat_trans_eq.
      {
        intro ; apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    Qed.

    Definition iso_comma_ump2_pr2
      : post_whisker iso_comma_ump2 iso_comma_pr2 = τ₂.
    Proof.
      use nat_trans_eq.
      {
        intro ; apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    Qed.

    (** The uniqueness *)
    Context {n₁ n₂ : Φ₁ ⟹ Φ₂}
            (n₁_pr1 : post_whisker n₁ iso_comma_pr1 = τ₁)
            (n₁_pr2 : post_whisker n₁ iso_comma_pr2 = τ₂)
            (n₂_pr1 : post_whisker n₂ iso_comma_pr1 = τ₁)
            (n₂_pr2 : post_whisker n₂ iso_comma_pr2 = τ₂).

    Definition iso_comma_ump_eq
      : n₁ = n₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      use pathsdirprod.
      - pose (nat_trans_eq_pointwise n₁_pr1 x) as q₁.
        pose (nat_trans_eq_pointwise n₂_pr1 x) as q₂.
        cbn in q₁, q₂.
        exact (q₁ @ !q₂).
      - pose (nat_trans_eq_pointwise n₁_pr2 x) as q₁.
        pose (nat_trans_eq_pointwise n₂_pr2 x) as q₂.
        cbn in q₁, q₂.
        exact (q₁ @ !q₂).
    Qed.
  End UniversalMappingProperty.
End IsoCommaCategory.

Definition univalent_iso_comma
           {C₁ C₂ C₃ : univalent_category}
           (F : C₁ ⟶ C₃)
           (G : C₂ ⟶ C₃)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (iso_comma F G).
  - apply is_univalent_iso_comma.
    + exact (pr2 C₁).
    + exact (pr2 C₂).
    + exact (pr2 C₃).
Defined.
