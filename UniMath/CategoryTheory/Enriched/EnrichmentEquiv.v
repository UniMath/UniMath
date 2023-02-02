Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Enriched.Enriched.
Require Import UniMath.CategoryTheory.Enriched.Enrichment.
Require Import UniMath.CategoryTheory.Enriched.UnderlyingCategory.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichmentToEnrichedCat.
  Context {V : monoidal_cat}
          (E : cat_with_enrichment V).

  Definition make_enriched_cat_data
    : enriched_precat_data V.
  Proof.
    simple refine (_ ,, (_ ,, (_ ,, _))).
    - exact E.
    - exact (λ x y, E ⦃ x , y ⦄).
    - exact (enriched_id E).
    - exact (enriched_comp E).
  Defined.

  Definition make_enriched_cat_id_ax
    : enriched_id_ax make_enriched_cat_data.
  Proof.
    intros x y.
    split ; cbn.
    - refine (!_).
      apply (pr2 E).
    - refine (!_).
      apply (pr2 E).
  Qed.

  Definition make_enriched_cat_assoc_ax
    : enriched_assoc_ax make_enriched_cat_data.
  Proof.
    intros w x y z ; cbn.
    rewrite !assoc.
    apply (pr2 E).
  Qed.

  Definition make_enriched_cat
    : enriched_precat V.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact make_enriched_cat_data.
    - exact make_enriched_cat_id_ax.
    - exact make_enriched_cat_assoc_ax.
  Defined.
End EnrichmentToEnrichedCat.

Definition cat_with_enrichment_help_data₁
           (V : monoidal_cat)
  : UU
  := ∑ (C : UU)
       (arr : C → C → V)
       (eI : ∏ (x : C), 𝟙 --> arr x x),
     ∏ (x y z : C), arr y z ⊗ arr x y --> arr x z.

Definition cat_with_enrichment_help_data₂
           {V : monoidal_cat}
           (E : cat_with_enrichment_help_data₁ V)
  : UU
  := let C := pr1 E in
     let arr := pr12 E in
     ∑ (mor : C → C → UU),
     (∏ (x : C), mor x x)
     ×
     (∏ (x y z : C), mor x y → mor y z → mor x z)
     ×
     (∏ (x y : C), mor x y → 𝟙 --> arr x y)
     ×
     (∏ (x y : C), 𝟙 --> arr x y → mor x y).

Definition path_cat_with_enrichment_help_data₂_help
           {V : monoidal_cat}
           {E : cat_with_enrichment_help_data₁ V}
           {C₁ C₂ : cat_with_enrichment_help_data₂ E}
           (C := pr1 E)
           (arr := pr12 E)
           (w : pr1 C₁ = pr1 C₂)
           (w_id : ∏ (x : C),
                   transportf
                     (λ A, A)
                     (maponpaths (λ A, A x x) w)
                     (pr12 C₁ x)
                   =
                   pr12 C₂ x)
  : UU.
Proof.
  refine (∏ (x y z : C) (f : pr1 C₁ x y) (g : pr1 C₁ y z),
           _
           =
           pr122 C₂ _ _ _ (w _ _ f) (w _ _ g)).
  refine .
  refine ().
  assert (pr1 C₁ x x = pr1 C₂ x x).
  {
    exact (maponpaths (λ A, A x x) w).
    Check maponpaths (λ A, A x x) w.
    induction w.
    refine (transportf (λ z, pr1 z x x) _ _).
  Search
  Check transportf pr12 C₁ x.
           (w_c : ∏ (x y z : C) (f : pr1 C₁ x y) (g : pr1 C₁ y z),
                  w _ _ (pr122 C₁ _ _ _ f g)
                  =
                  pr122 C₂ _ _ _ (w _ _ f) (w _ _ g))
           (w_l : ∏ (x y : C) (f : pr1 C₁ x y),
                  pr1 (pr222 C₁) x y f
                  =
                  pr1 (pr222 C₂) x y (w _ _ f))
           (w_r : ∏ (x y : C) (f : 𝟙 --> arr x y),
                  w _ _ (pr2 (pr222 C₁) x y f)
                  =
                  pr2 (pr222 C₂) _ _ f)
  : C₁ = C₂.
Proof.
Admitted.

Definition path_cat_with_enrichment_help_data₂_help'
           {V : monoidal_cat}
           {E : cat_with_enrichment_help_data₁ V}
           {C₁ C₂ : cat_with_enrichment_help_data₂ E}
           (C := pr1 E)
           (arr := pr12 E)
           (w : ∏ (x y : C), pr1 C₁ x y = pr1 C₂ x y)
           (w_id : ∏ (x : C), w x x (pr12 C₁ x) = pr12 C₂ _)
           (w_c : ∏ (x y z : C) (f : pr1 C₁ x y) (g : pr1 C₁ y z),
                  w _ _ (pr122 C₁ _ _ _ f g)
                  =
                  pr122 C₂ _ _ _ (w _ _ f) (w _ _ g))
           (w_l : ∏ (x y : C) (f : pr1 C₁ x y),
                  pr1 (pr222 C₁) x y f
                  =
                  pr1 (pr222 C₂) x y (w _ _ f))
           (w_r : ∏ (x y : C) (f : 𝟙 --> arr x y),
                  w _ _ (pr2 (pr222 C₁) x y f)
                  =
                  pr2 (pr222 C₂) _ _ f)
  : C₁ = C₂.
Proof.
Admitted.

Definition path_cat_with_enrichment_help_data₂
           {V : monoidal_cat}
           {E : cat_with_enrichment_help_data₁ V}
           {C₁ C₂ : cat_with_enrichment_help_data₂ E}
           (C := pr1 E)
           (arr := pr12 E)
           (w : ∏ (x y : C), pr1 C₁ x y ≃ pr1 C₂ x y)
           (w_id : ∏ (x : C), w x x (pr12 C₁ x) = pr12 C₂ _)
           (w_c : ∏ (x y z : C) (f : pr1 C₁ x y) (g : pr1 C₁ y z),
                  w _ _ (pr122 C₁ _ _ _ f g)
                  =
                  pr122 C₂ _ _ _ (w _ _ f) (w _ _ g))
           (w_l : ∏ (x y : C) (f : pr1 C₁ x y),
                  pr1 (pr222 C₁) x y f
                  =
                  pr1 (pr222 C₂) x y (w _ _ f))
           (w_r : ∏ (x y : C) (f : 𝟙 --> arr x y),
                  w _ _ (pr2 (pr222 C₁) x y f)
                  =
                  pr2 (pr222 C₂) _ _ f)
  : C₁ = C₂.
Proof.
Admitted.

Definition cat_with_enrichment_help_data
           (V : monoidal_cat)
  : UU
  := ∑ (E : cat_with_enrichment_help_data₁ V),
     cat_with_enrichment_help_data₂ E.

Definition precategory_data_of_cat_with_enrichment_help_data
           {V : monoidal_cat}
           (E : cat_with_enrichment_help_data V)
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + apply E.
    + apply E.
  - intros ; cbn.
    apply (pr2 E).
  - intros x y z f g ; cbn in *.
    exact (pr1 (pr222 E) x y z f g).
Defined.

Definition enrichment_data_of_cat_with_enrichment_help_data
           {V : monoidal_cat}
           (E : cat_with_enrichment_help_data V)
  : enrichment_data
      (precategory_data_of_cat_with_enrichment_help_data E)
      V.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _) ; cbn.
  - intros x y.
    exact (pr121 E x y).
  - cbn.
    intros x.
    exact (pr1 (pr221 E) x).
  - cbn ; intros x y z.
    exact (pr2 (pr221 E) x y z).
  - apply (pr2 E).
  - apply (pr2 E).
Defined.

Definition cat_with_enrichment_help
           (V : monoidal_cat)
  := ∑ (CE : cat_with_enrichment_help_data V),
     let C := precategory_data_of_cat_with_enrichment_help_data CE in
     let E := enrichment_data_of_cat_with_enrichment_help_data CE in
     enrichment_laws E × is_precategory C × has_homsets C.

Definition cat_with_enrichment_weq_cat_with_enrichment_help
           (V : monoidal_cat)
  : cat_with_enrichment V ≃ cat_with_enrichment_help V.
Proof.
  use weq_iso.
  - intros E.
    simple refine (((_ ,, _ ,, _ ,, _) ,, _ ,, _ ,, _ ,, _ ,, _) ,, (_ ,, _ ,, _)).
    + exact (pr11 (pr111 E)).
    + exact (pr112 E).
    + exact (pr1 (pr212 E)).
    + exact (pr12 (pr212 E)).
    + exact (pr21 (pr111 E)).
    + exact (pr12 (pr111 E)).
    + exact (pr22 (pr111 E)).
    + exact (pr122 (pr212 E)).
    + exact (pr222 (pr212 E)).
    + exact (pr22 E).
    + exact (pr211 E).
    + exact (pr21 E).
  - intros E.
    simple refine (_ ,, _ ,, _).
    + simple refine ((((_ ,, _) ,, _ ,, _) ,, _) ,, _).
      * exact (pr111 E).
      * exact (pr121 E).
      * exact (pr1 (pr221 E)).
      * exact (pr12 (pr221 E)).
      * exact (pr122 E).
      * exact (pr222 E).
    + simple refine (_ ,, _ ,, _ ,, _ ,, _).
      * exact (pr1 (pr211 E)).
      * exact (pr12 (pr211 E)).
      * exact (pr22 (pr211 E)).
      * exact (pr122 (pr221 E)).
      * exact (pr222 (pr221 E)).
    + exact (pr12 E).
  - intro E ; apply idpath.
  - intro E ; apply idpath.
Defined.

Definition enriched_precat_weq_cat_with_enrichment
           (V : monoidal_cat)
  : enriched_precat V ≃ cat_with_enrichment V.
Proof.
  use weq_iso.
  - exact (underlying_cat_with_enrichment V).
  - exact make_enriched_cat.
  - intro C.
    use subtypePath.
    {
      intro ; apply isapropdirprod.
      + repeat (use impred ; intro) ; cbn -[isofhlevel].
        apply isapropdirprod ; apply homset_property.
      + repeat (use impred ; intro) ; cbn -[isofhlevel].
        apply homset_property.
    }
    cbn.
    apply idpath.
  - intro C.
    use (invmaponpathsweq (cat_with_enrichment_weq_cat_with_enrichment_help V)).
    use subtypePath.
    {
      intro z.
      use invproofirrelevance.
      intros φ₁ φ₂.
      repeat (use pathsdirprod) ;
        repeat (use funextsec ; intro) ;
        try (apply homset_property) ;
        try (apply φ₁) ;
        apply isapropiscontr.
    }
    cbn.
    apply maponpaths.
    use path_cat_with_enrichment_help_data₂.
    + intros x y ; cbn.
      use weq_iso.
      * exact (pr222 (pr212 C) x y).
      * exact (pr122 (pr212 C) x y).
      * admit.
      * admit.
    + cbn.
      intros x.
      exact (pr12 (pr222 (pr222 C)) x).
    + cbn.
      intros x y z f g.
      refine (!_).
      pose (pr22 (pr222 (pr222 C)) x y z (enriched_to_arr (pr12 C) f) (enriched_to_arr (pr12 C) g)).
      cbn in p.
      refine (p @ _).
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      admit.
    + cbn.
      intros x y f.
      admit.
    + cbn.
      intros x y f.
      admit.
Admitted.
