(*****************************************************************

 Equivalence of enrichments and enriched categories

 We have two notions of enriched categories: one is the usual
 definition that can be found in textbooks and the other makes
 use of enrichments. In this file, we prove that these two notions
 are actually equivalent.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalCategories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.UnderlyingCategory.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor.

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

Definition cat_with_enrichment_alt_data_help
           {V : monoidal_cat}
           (ob : UU)
           (arr : ob -> ob -> V)
  : UU
  := ∑ (mor : ob -> ob -> UU),
     (∏ (x : ob), mor x x)
     ×
     (∏ (x y z : ob), mor x y → mor y z → mor x z)
     ×
     (∏ (x y : ob), mor x y → 𝟙 --> arr x y)
     ×
     (∏ (x y : ob), 𝟙 --> arr x y → mor x y).

Definition path_cat_with_enrichment_alt_data_help_lemma
           {V : monoidal_cat}
           {ob : UU}
           {arr : ob -> ob -> V}
           {E₁ E₂ : cat_with_enrichment_alt_data_help ob arr}
           (p : pr1 E₁ = pr1 E₂)
           (q₁ : ∏ (x : ob),
                 transportf (λ T, T x x) p (pr12 E₁ x)
                 =
                 pr12 E₂ x)
           (q₂ : ∏ (x y z : ob)
                   (g₁ : pr1 E₁ x y)
                   (g₂ : pr1 E₁ y z),
                 transportf
                   (λ T, T x z)
                   p
                   (pr122 E₁ _ _ _ g₁ g₂)
                 =
                 pr122 E₂ _ _ _
                     (transportf (λ T, T x y) p g₁)
                     (transportf (λ T, T y z) p g₂))
           (q₃ : ∏ (x y : ob) (g : pr1 E₁ x y),
                 (pr1 (pr222 E₁)) _ _ g
                 =
                 (pr1 (pr222 E₂)) _ _ (transportf (λ T, T x y) p g))
           (q₄ : ∏ (x y : ob) (g : 𝟙 --> arr x y),
                 transportf (λ T, T x y) p (pr2 (pr222 E₁) _ _ g)
                 =
                 pr2 (pr222 E₂) _ _ g)
  : E₁ = E₂.
Proof.
  induction E₁ as [ D₁ E₁ ].
  induction E₂ as [ D₂ E₂ ].
  cbn in *.
  induction p.
  cbn in *.
  apply maponpaths.
  repeat (use pathsdirprod).
  - use funextsec ; intro.
    apply q₁.
  - repeat (use funextsec ; intro).
    apply q₂.
  - repeat (use funextsec ; intro).
    apply q₃.
  - repeat (use funextsec ; intro).
    apply q₄.
Qed.

Definition fam_eq
           {X : UU}
           {Y₁ Y₂ : X → X → UU}
           (p : ∏ (x₁ x₂ : X), Y₁ x₁ x₂ ≃ Y₂ x₁ x₂)
  : Y₁ = Y₂.
Proof.
  use funextsec ; intro x₁.
  use funextsec ; intro x₂.
  exact (invmap (univalence (Y₁ x₁ x₂) (Y₂ x₁ x₂)) (p x₁ x₂)).
Defined.

Definition transportf_fam_eq
           {X : UU}
           {Y₁ Y₂ : X → X → UU}
           (p : ∏ (x₁ x₂ : X), Y₁ x₁ x₂ ≃ Y₂ x₁ x₂)
           {x₁ x₂ : X}
           (y : Y₁ x₁ x₂)
  : transportf
      (λ T, T _ _)
      (fam_eq p)
      y
    =
    p x₁ x₂ y.
Proof.
  unfold fam_eq.
  etrans.
  {
    apply (transportf_funextfun (λ T, T x₂)).
  }
  etrans.
  {
    apply (transportf_funextfun (idfun UU)).
  }
  cbn.
  rewrite pr1_eqweqmap.
  exact (maponpaths
           (λ z, pr1 z y)
           (homotweqinvweq (univalence (Y₁ x₁ x₂) (Y₂ x₁ x₂)) (p x₁ x₂))).
Qed.

Definition path_cat_with_enrichment_alt_data_help
           {V : monoidal_cat}
           {ob : UU}
           {arr : ob -> ob -> V}
           {E₁ E₂ : cat_with_enrichment_alt_data_help ob arr}
           (f : ∏ (x y : ob), pr1 E₁ x y → pr1 E₂ x y)
           (Hf : ∏ (x y : ob), isweq (f x y))
           (p₁ : ∏ (x : ob), f _ _ (pr12 E₁ x) = pr12 E₂ x)
           (p₂ : ∏ (x y z : ob)
                   (g₁ : pr1 E₁ x y)
                   (g₂ : pr1 E₁ y z),
                 f _ _ (pr122 E₁ _ _ _ g₁ g₂)
                 =
                 pr122 E₂ _ _ _ (f _ _ g₁) (f _ _ g₂))
           (p₃ : ∏ (x y : ob) (g : pr1 E₁ x y),
                 (pr1 (pr222 E₁)) _ _ g
                 =
                 (pr1 (pr222 E₂)) _ _ (f _ _ g))
           (p₄ : ∏ (x y : ob) (g : 𝟙 --> arr x y),
                 f _ _ (pr2 (pr222 E₁) _ _ g)
                 =
                 pr2 (pr222 E₂) _ _ g)
  : E₁ = E₂.
Proof.
  use path_cat_with_enrichment_alt_data_help_lemma.
  - use fam_eq.
    intros x₁ x₂.
    use make_weq.
    + exact (f x₁ x₂).
    + exact (Hf x₁ x₂).
  - intros x.
    rewrite transportf_fam_eq.
    apply p₁.
  - intros x y z g₁ g₂.
    rewrite !transportf_fam_eq.
    apply p₂.
  - intros x y g.
    rewrite !transportf_fam_eq.
    apply p₃.
  - intros x y g.
    rewrite !transportf_fam_eq.
    apply p₄.
Qed.

Definition cat_with_enrichment_alt_data
           (V : monoidal_cat)
  : UU
  := ∑ (ob : UU)
       (arr : ob -> ob -> V),
     (∏ (x : ob), 𝟙 --> arr x x)
     ×
     (∏ (x y z : ob), arr y z ⊗ arr x y --> arr x z)
     ×
     cat_with_enrichment_alt_data_help ob arr.

Definition cat_with_enrichment_alt_data_precategory_data
           {V : monoidal_cat}
           (E : cat_with_enrichment_alt_data V)
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (pr1 E).
    + exact (pr12 (pr222 E)).
  - exact (pr122 (pr222 E)).
  - exact (pr1 (pr222 (pr222 E))).
Defined.

Definition cat_with_enrichment_alt_data_enrichment
           {V : monoidal_cat}
           (E : cat_with_enrichment_alt_data V)
  : enrichment_data (cat_with_enrichment_alt_data_precategory_data E) V.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (pr12 E).
  - exact (pr122 E).
  - exact (pr1 (pr222 E)).
  - exact (pr12 (pr222 (pr222 E))).
  - exact (pr22 (pr222 (pr222 E))).
Defined.

Definition cat_with_enrichment_alt_laws
           {V : monoidal_cat}
           (E : cat_with_enrichment_alt_data V)
  : UU
  := has_homsets (cat_with_enrichment_alt_data_precategory_data E)
     ×
     is_precategory (cat_with_enrichment_alt_data_precategory_data E)
     ×
     enrichment_laws (cat_with_enrichment_alt_data_enrichment E).

Definition cat_with_enrichment_alt
           (V : monoidal_cat)
  : UU
  := ∑ (E : cat_with_enrichment_alt_data V), cat_with_enrichment_alt_laws E.

Definition cat_with_enrichment_to_alt
           {V : monoidal_cat}
           (E : cat_with_enrichment V)
  : cat_with_enrichment_alt V.
Proof.
  simple refine ((_ ,, (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _)) ,, _).
  - exact (ob (pr1 E)).
  - exact (pr11 (pr2 E)).
  - exact (pr121 (pr2 E)).
  - exact (pr1 (pr221 (pr2 E))).
  - exact (pr21 (pr111 E)).
  - apply identity.
  - exact (λ _ _ _ f g, f · g).
  - exact (pr12 (pr221 (pr2 E))).
  - exact (pr22 (pr221 (pr2 E))).
  - simple refine (_ ,, _ ,, _).
    + apply homset_property.
    + exact (pr211 E).
    + exact (pr22 E).
Defined.

Definition cat_with_enrichment_from_alt
           {V : monoidal_cat}
           (E : cat_with_enrichment_alt V)
  : cat_with_enrichment V.
Proof.
  simple refine (((((_ ,, _) ,, (_ ,, _)) ,, _) ,, _) ,, _).
  - exact (pr11 E).
  - exact (pr122 (pr221 E)).
  - exact (pr1 (pr222 (pr221 E))).
  - exact (pr12 (pr222 (pr221 E))).
  - exact (pr122 E).
  - exact (pr12 E).
  - simple refine ((_ ,, _ ,, _ ,, _ ,, _) ,, _).
    + exact (pr121 E).
    + exact (pr1 (pr221 E)).
    + exact (pr12 (pr221 E)).
    + exact (pr122 (pr222 (pr221 E))).
    + exact (pr222 (pr222 (pr221 E))).
    + exact (pr222 E).
Defined.

Definition cat_with_enrichment_weq_alt
           (V : monoidal_cat)
  : cat_with_enrichment V ≃ cat_with_enrichment_alt V.
Proof.
  use weq_iso.
  - exact cat_with_enrichment_to_alt.
  - exact cat_with_enrichment_from_alt.
  - intro E.
    apply idpath.
  - intro E.
    apply idpath.
Defined.

Definition enriched_precat_weq_cat_with_enrichment_inv_left
           {V : monoidal_cat}
           (E : enriched_precat V)
  : make_enriched_cat (underlying_cat_with_enrichment V E)
    =
    E.
Proof.
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
Qed.

Definition enriched_precat_weq_cat_with_enrichment_inv_right
           {V : monoidal_cat}
           (E : cat_with_enrichment V)
  : underlying_cat_with_enrichment V (make_enriched_cat E)
    =
    E.
Proof.
    use (invmaponpathsweq (cat_with_enrichment_weq_alt V)).
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
    do 4 apply maponpaths.
    use path_cat_with_enrichment_alt_data_help.
    - exact (λ x y f, enriched_to_arr (pr2 E) f).
    - apply isweq_enriched_to_arr.
    - cbn.
      intro x.
      rewrite enriched_to_arr_id.
      apply idpath.
    - cbn.
      intros x y z f g.
      rewrite (enriched_to_arr_comp (pr2 E)).
      rewrite !enriched_from_to_arr.
      apply idpath.
    - cbn.
      intros x y f.
      refine (!_).
      apply enriched_from_to_arr.
    - cbn.
      intros x y f.
      apply idpath.
Qed.

Definition enriched_precat_weq_cat_with_enrichment
           (V : monoidal_cat)
  : enriched_precat V ≃ cat_with_enrichment V.
Proof.
  use weq_iso.
  - exact (underlying_cat_with_enrichment V).
  - exact make_enriched_cat.
  - exact enriched_precat_weq_cat_with_enrichment_inv_left.
  - exact enriched_precat_weq_cat_with_enrichment_inv_right.
Defined.
