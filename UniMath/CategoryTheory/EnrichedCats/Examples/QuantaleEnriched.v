(*******************************************************************************************

 Categories enriched over quantales

 Categories enriched over quantales give a simpler class of enriched categories. In essence,
 these are more like generalized posets: their types of objects are a set and there is at
 most one morphism between any two objects. This is caused by the fact that quantales are
 posets, and thus there is at most one morphism from the unit to any object. In this file,
 we give specialized builders for quantale enriched categories, quantale enriched functors,
 and quantale enriched profunctors. We also give specialized equality principles.

 Content
 1. Builder for categories enriched over quantales
 2. The objects in a quantale enriched univalent category form a set
 3. Builder for functors of categories enriched over quantales
 4. Properties of quantale enriched functors
 5. Equality of natural transformation for quantale enriched categories
 6. Builder for quantale enriched profunctors
 7. Properties of quantale enriched profunctors
 8. Properties of quantale enriched transformations

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section QuantaleEnriched.
  Context (V : quantale_cosmos).

  Definition quantale_faithful
    : faithful_moncat V.
  Proof.
    intro ; intros.
    apply is_poset_category_quantale_cosmos.
  Qed.

  (** * 1. Builder for categories enriched over quantales *)
  Section QuantaleEnrichmentBuilder.
    Context (X : hSet)
            (R : X → X → V)
            (Ri : ∏ (x : X), I_{V} --> R x x)
            (Rc : ∏ (x y z : X), R y z ⊗ R x y --> R x z)
            (Rp : ∏ (x y : X), I_{V} --> R x y → I_{V} --> R y x → x = y).

    Definition make_quantale_enrichment_precategory_ob_mor
      : precategory_ob_mor.
    Proof.
      use make_precategory_ob_mor.
      - exact X.
      - exact (λ x y, I_{V} --> R x y).
    Defined.

    Definition make_quantale_enrichment_precategory_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - exact make_quantale_enrichment_precategory_ob_mor.
      - exact Ri.
      - exact (λ x y z f g, mon_linvunitor _ · g #⊗ f · Rc x y z).
    Defined.

    Proposition make_quantale_enrichment_precategory_laws
      : is_precategory make_quantale_enrichment_precategory_data.
    Proof.
      repeat split ; intro ; intros ; cbn ; apply is_poset_category_quantale_cosmos.
    Qed.

    Definition make_quantale_enrichment_precategory
      : precategory.
    Proof.
      use make_precategory.
      - exact make_quantale_enrichment_precategory_data.
      - exact make_quantale_enrichment_precategory_laws.
    Defined.

    Definition make_quantale_enrichment_category
      : category.
    Proof.
      use make_category.
      - exact make_quantale_enrichment_precategory.
      - abstract
          (intros x y ;
           apply isasetaprop ;
           apply is_poset_category_quantale_cosmos).
    Defined.

    Proposition is_univalent_make_quantale_enrichment_category
      : is_univalent make_quantale_enrichment_category.
    Proof.
      intros x y.
      use isweqimplimpl.
      - intro f.
        use Rp.
        + exact f.
        + exact (inv_from_z_iso f).
      - apply setproperty.
      - use isaproptotal2.
        + intro.
          apply isaprop_is_z_isomorphism.
        + intros.
          apply is_poset_category_quantale_cosmos.
    Qed.

    Definition make_quantale_enrichment_univalent_category
      : univalent_category.
    Proof.
      use make_univalent_category.
      - exact make_quantale_enrichment_category.
      - exact is_univalent_make_quantale_enrichment_category.
    Defined.

    Definition is_poset_quantale_enrichment_univalent_category
      : is_poset_category make_quantale_enrichment_univalent_category.
    Proof.
      intros x y.
      apply is_poset_category_quantale_cosmos.
    Qed.

    Definition make_quantale_enrichment_data
      : enrichment_data make_quantale_enrichment_category V
      := R ,, Ri ,, Rc ,, (λ x y f, f) ,, (λ x y f, f).

    Proposition make_quantale_enrichment_laws
      : enrichment_laws make_quantale_enrichment_data.
    Proof.
      repeat split ; intro ; intros ; cbn ; apply is_poset_category_quantale_cosmos.
    Qed.

    Definition make_quantale_enrichment
      : enrichment make_quantale_enrichment_category V
      := make_quantale_enrichment_data ,, make_quantale_enrichment_laws.
  End QuantaleEnrichmentBuilder.

  (** * 2. The objects in a quantale enriched univalent category form a set *)
  Proposition isaprop_mor_quantale_enrichment_univalent_cat
              {C : category}
              (E : enrichment C V)
              (x y : C)
    : isaprop (x --> y).
  Proof.
    use invproofirrelevance.
    intros f g.
    refine (pr1 (isofhlevelweqf 1 (make_weq _ (isweq_enriched_to_arr E x y)) _ f g)).
    apply is_poset_category_quantale_cosmos.
  Qed.

  Proposition isaset_ob_quantale_enrichment_univalent_cat
              {C : univalent_category}
              (E : enrichment C V)
    : isaset C.
  Proof.
    intros x y.
    use (isofhlevelweqb 1 (make_weq _ (univalent_category_is_univalent C x y))).
    use isaproptotal2.
    - intro.
      apply isaprop_is_z_isomorphism.
    - intros f g Hf Hg.
      apply (isaprop_mor_quantale_enrichment_univalent_cat E).
  Qed.

  (** * 3. Builder for functors of categories enriched over quantales *)
  Section QuantaleEnrichmentFunctorBuilder.
    Context {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (F : C₁ → C₂)
            (Fm : ∏ (x y : C₁), E₁ ⦃ x, y ⦄ --> E₂ ⦃ F x, F y ⦄).

    Definition make_functor_quantale_enrichment_data
      : functor_data C₁ C₂.
    Proof.
      use make_functor_data.
      - exact F.
      - exact (λ x y f, enriched_to_arr E₂ (enriched_from_arr E₁ f · Fm x y)).
    Defined.

    Proposition make_functor_quantale_enrichment_laws
      : is_functor make_functor_quantale_enrichment_data.
    Proof.
      split ; intro ; intros ; apply (isaprop_mor_quantale_enrichment_univalent_cat E₂).
    Qed.

    Definition make_functor_quantale_enrichment
      : C₁ ⟶ C₂.
    Proof.
      use make_functor.
      - exact make_functor_quantale_enrichment_data.
      - exact make_functor_quantale_enrichment_laws.
    Defined.

    Definition make_functor_enrichment_quantale_enrichment
      : functor_enrichment
          make_functor_quantale_enrichment
          E₁
          E₂.
    Proof.
      simple refine (_ ,, _).
      - exact Fm.
      - abstract
          (repeat split ; intro ; intros ; apply is_poset_category_quantale_cosmos).
    Defined.
  End QuantaleEnrichmentFunctorBuilder.

  (** * 4. Properties of quantale enriched functors *)
  Proposition isaset_functor_quantale_enrichment
              {C₁ C₂ : univalent_category}
              (E₂ : enrichment C₂ V)
    : isaset (C₁ ⟶ C₂).
  Proof.
    use isaset_total2.
    - use isaset_total2.
      + use funspace_isaset.
        use isaset_ob_quantale_enrichment_univalent_cat.
        exact E₂.
      + intro F.
        use impred_isaset ; intro x.
        use impred_isaset ; intro y.
        use impred_isaset ; intro f.
        apply homset_property.
    - intro.
      apply isasetaprop.
      apply isaprop_is_functor.
      apply homset_property.
  Qed.

  Proposition eq_functor_quantale_enrichment
              {C₁ C₂ : category}
              (E₂ : enrichment C₂ V)
              {F G : C₁ ⟶ C₂}
              (p : ∏ (x : C₁), F x = G x)
    : F = G.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_functor.
      apply homset_property.
    }
    use subtypePath.
    {
      intro.
      repeat (use impred ; intro).
      apply isaprop_mor_quantale_enrichment_univalent_cat.
      exact E₂.
    }
    use funextsec.
    exact p.
  Qed.

  (** * 5. Equality of natural transformation for quantale enriched categories *)
  Proposition nat_trans_eq_quantale_enrichment
              {C₁ C₂ : category}
              {F G : C₁ ⟶ C₂}
              (τ θ : F ⟹ G)
              (E₂ : enrichment C₂ V)
    : τ = θ.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro.
    apply isaprop_mor_quantale_enrichment_univalent_cat.
    exact E₂.
  Qed.

  (** * 6. Builder for quantale enriched profunctors *)
  Definition make_quantale_enriched_profunctor_data
             {C₁ C₂ : category}
             {E₁ : enrichment C₁ V}
             {E₂ : enrichment C₂ V}
             (P : C₂ → C₁ → V)
             (Pl : ∏ (x₁ x₂ : C₂)
                     (y : C₁),
                   E₂ ⦃ x₂, x₁ ⦄ ⊗ P x₁ y --> P x₂ y)
             (Pr : ∏ (x : C₂)
                     (y₁ y₂ : C₁),
                   E₁ ⦃ y₁, y₂ ⦄ ⊗ P x y₁ --> P x y₂)
    : enriched_profunctor_data E₁ E₂.
  Proof.
    use make_enriched_profunctor_data.
    - exact P.
    - exact Pl.
    - exact Pr.
  Defined.

  Definition make_quantale_enriched_profunctor
             {C₁ C₂ : category}
             {E₁ : enrichment C₁ V}
             {E₂ : enrichment C₂ V}
             (P : C₂ → C₁ → V)
             (Pl : ∏ (x₁ x₂ : C₂)
                     (y : C₁),
                   E₂ ⦃ x₂, x₁ ⦄ ⊗ P x₁ y --> P x₂ y)
             (Pr : ∏ (x : C₂)
                     (y₁ y₂ : C₁),
                   E₁ ⦃ y₁, y₂ ⦄ ⊗ P x y₁ --> P x y₂)
    : E₁ ↛e E₂.
  Proof.
    use make_enriched_profunctor.
    - exact (make_quantale_enriched_profunctor_data P Pl Pr).
    - abstract
        (repeat split ;
         intros ;
         apply (isaprop_mor_quantale_enrichment_univalent_cat (self_enrichment V))).
  Defined.

  (** * 7. Properties of quantale enriched profunctors *)
  Proposition isaset_profunctor_quantale_enrichment
              {C₁ C₂ : univalent_category}
              (E₁ : enrichment C₁ V)
              (E₂ : enrichment C₂ V)
    : isaset (E₁ ↛e E₂).
  Proof.
    use isaset_total2.
    - use isaset_total2.
      + use funspace_isaset.
        use funspace_isaset.
        exact (@isaset_ob_quantale_enrichment_univalent_cat
                 (univalent_category_of_quantale_cosmos V)
                 (self_enrichment V)).
      + intro F.
        use isasetdirprod.
        * use impred_isaset ; intro x₁.
          use impred_isaset ; intro x₂.
          use impred_isaset ; intro y.
          apply homset_property.
        * use impred_isaset ; intro x.
          use impred_isaset ; intro y₁.
          use impred_isaset ; intro y₂.
          apply homset_property.
    - intro.
      apply isasetaprop.
      apply isaprop_enriched_profunctor_laws.
  Qed.

  Proposition eq_profunctor_quantale_enrichment
              {C₁ C₂ : category}
              {E₁ : enrichment C₁ V}
              {E₂ : enrichment C₂ V}
              (P Q : E₁ ↛e E₂)
              (p : ∏ (y : C₂) (x : C₁), P y x = Q y x)
    : P = Q.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enriched_profunctor_laws.
    }
    use subtypePath.
    {
      intro.
      use isapropdirprod ;
      repeat (use impred ; intro) ;
      apply (isaprop_mor_quantale_enrichment_univalent_cat (self_enrichment V)).
    }
    use funextsec ; intro y.
    use funextsec ; intro x.
    exact (p y x).
  Qed.

  (** * 8. Properties of quantale enriched transformations *)
  Proposition eq_quantale_enriched_profunctor_transformation
              {C₁ C₂ : category}
              {E₁ : enrichment C₁ V}
              {E₂ : enrichment C₂ V}
              {P Q : E₁ ↛e E₂}
              (τ θ : enriched_profunctor_transformation P Q)
    : τ = θ.
  Proof.
    use eq_enriched_profunctor_transformation.
    intros y x.
    apply (isaprop_mor_quantale_enrichment_univalent_cat (self_enrichment V)).
  Qed.

  Proposition isaprop_quantale_enriched_profunctor_transformation
              {C₁ C₂ : category}
              {E₁ : enrichment C₁ V}
              {E₂ : enrichment C₂ V}
              (P Q : E₁ ↛e E₂)
    : isaprop (enriched_profunctor_transformation P Q).
  Proof.
    use invproofirrelevance.
    intros τ θ.
    apply eq_quantale_enriched_profunctor_transformation.
  Qed.
End QuantaleEnriched.
