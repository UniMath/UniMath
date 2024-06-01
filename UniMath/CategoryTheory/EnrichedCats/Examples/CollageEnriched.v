(******************************************************************************************

 The collage of an enriched profunctor

 A fundamental construction on enriched profunctors is given by the collage (also known as
 the cograph). The collage of an enriched profunctor `E₁ ↛e E₂` is given by the enriched
 category defined as follows:
 - objects: `E₁ ⨿ E₂`
 - morphisms from `x₁ : E₁` to `x₂ : E₁`: morphisms in `E₁`
 - morphisms from `y₁ : E₂` to `x₂ : E₁`: morphisms from `I_{V}` to the initial object
 - morphisms from `x₁ : E₁` to `y₂ : E₂`: `I_{V} --> P y₁ x₁`
 - morphisms from `y₁ : E₂` to `y₂ : E₂`: morphisms in `E₂`
 Essentially, the morphisms between objects from `E₁` are given by morphisms in `E₂`, and
 similarly for `E₂`. Morphisms from an object in `E₁` to an object `E₂` are determined by
 the profunctor `P`, whereas morphisms from an object in `E₂` to an object in `E₁` are given
 by the initial object. If we were looking at set-enriched profunctors, then there would be
 no morphisms from something in `E₂` to something in `E₁`.

 In this file, we define the collage of an enriched profunctor, and we show that it gives
 rise to an opspan whose legs are fully faithful enriched functors. In addition, we show
 that under mild assumptions this gives rise to a univalent category (the assumption being
 that there is no morphism from the unit of the monoidal category to the initial object).
 Note that the collage of a profunctor is an instance of a colimit. As such, if the
 aforementioned condition is not satisfied, then we could take its Rezk completion to
 acquire the desired univalent category (where, if necessary, we need to mind a potential
 increase in the universe level).

 References
 - "Fibrations in bicategories" by Street
 - "Categorical notions of fibration" by Loregian and Riehl

 Content
 1. The underlying category
 2. The enrichment
 3. The underlying category
 4. The underlying category is univalent
 5. The left inclusion
 6. The right inclusion
 7. The square of the collage

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

#[local] Opaque sym_mon_braiding.

Section CollageOfProfunctor.
  Context {V : benabou_cosmos}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : E₁ ↛e E₂).

  Let IV : Initial V := benabou_cosmos_initial V.

  (** * 1. The underlying category *)
  Definition enriched_profunctor_collage_mor
             (x₁ x₂ : C₁ ⨿ C₂)
    : UU.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ; induction x₂ as [ x₂ | y₂ ].
    - exact (x₁ --> x₂).
    - exact (I_{V} --> IV).
    - exact (I_{V} --> P y₁ x₂).
    - exact (y₁ --> y₂).
  Defined.

  Definition enriched_profunctor_collage_id
             (x : C₁ ⨿ C₂)
    : enriched_profunctor_collage_mor x x.
  Proof.
    induction x as [ x | y ].
    - exact (identity x).
    - exact (identity y).
  Defined.

  Definition enriched_profunctor_collage_comp
             {x₁ x₂ x₃ : C₁ ⨿ C₂}
             (f : enriched_profunctor_collage_mor x₁ x₂)
             (g : enriched_profunctor_collage_mor x₂ x₃)
    : enriched_profunctor_collage_mor x₁ x₃.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      induction x₃ as [ x₃ | y₃ ] ;
      cbn in *.
    - exact (f · g).
    - exact g.
    - use (enriched_to_arr E₁).
      refine (f · _).
      apply InitialArrow.
    - exact f.
    - exact (f · rmap_e_arr P g y₁).
    - use (enriched_to_arr E₂).
      refine (g · _).
      apply InitialArrow.
    - exact (g · lmap_e_arr P x₃ f).
    - exact (f · g).
  Defined.

  Definition enriched_profunctor_collage_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (C₁ ⨿ C₂).
    - exact enriched_profunctor_collage_mor.
  Defined.

  Definition enriched_profunctor_collage_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact enriched_profunctor_collage_precategory_ob_mor.
    - exact enriched_profunctor_collage_id.
    - exact (λ _ _ _ f g, enriched_profunctor_collage_comp f g).
  Defined.

  (** * 2. The enrichment *)
  Definition enriched_profunctor_collage_enrichment_hom_ob
             (x₁ x₂ : enriched_profunctor_collage_precategory_data)
    : V.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      cbn.
    - exact (E₁ ⦃ x₁ , x₂ ⦄).
    - exact IV.
    - exact (P y₁ x₂).
    - exact (E₂ ⦃ y₁ , y₂ ⦄).
  Defined.

  Definition enriched_profunctor_collage_enrichment_id
             (x : enriched_profunctor_collage_precategory_data)
    : I_{ V} --> enriched_profunctor_collage_enrichment_hom_ob x x.
  Proof.
    induction x as [ x | y ] ; cbn in *.
    - apply enriched_id.
    - apply enriched_id.
  Defined.

  Definition enriched_profunctor_collage_enrichment_comp
             (x₁ x₂ x₃ : enriched_profunctor_collage_precategory_data)
    : enriched_profunctor_collage_enrichment_hom_ob x₂ x₃
      ⊗ enriched_profunctor_collage_enrichment_hom_ob x₁ x₂
      -->
      enriched_profunctor_collage_enrichment_hom_ob x₁ x₃.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      induction x₃ as [ x₃ | y₃ ] ;
      cbn in *.
    - apply enriched_comp.
    - apply arrow_from_tensor_initial_r_benabou_cosmos.
    - apply arrow_from_tensor_initial_l_benabou_cosmos.
    - apply arrow_from_tensor_initial_l_benabou_cosmos.
    - apply (rmap_e P).
    - apply arrow_from_tensor_initial_r_benabou_cosmos.
    - exact (sym_mon_braiding _ _ _ · lmap_e P _ _ _).
    - apply enriched_comp.
  Defined.

  Definition enriched_profunctor_collage_enrichment_from_arr
             {x₁ x₂ : enriched_profunctor_collage_precategory_data}
             (f : x₁ --> x₂)
    : I_{ V} --> enriched_profunctor_collage_enrichment_hom_ob x₁ x₂.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      cbn in *.
    - exact (enriched_from_arr E₁ f).
    - exact f.
    - exact f.
    - exact (enriched_from_arr E₂ f).
  Defined.

  Definition enriched_profunctor_collage_enrichment_to_arr
             {x₁ x₂ : enriched_profunctor_collage_precategory_data}
             (f : I_{ V} --> enriched_profunctor_collage_enrichment_hom_ob x₁ x₂)
    : x₁ --> x₂.
  Proof.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      cbn in *.
    - exact (enriched_to_arr E₁ f).
    - exact f.
    - exact f.
    - exact (enriched_to_arr E₂ f).
  Defined.

  Definition enriched_profunctor_collage_enrichment_data
    : enrichment_data enriched_profunctor_collage_precategory_data V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact enriched_profunctor_collage_enrichment_hom_ob.
    - exact enriched_profunctor_collage_enrichment_id.
    - exact enriched_profunctor_collage_enrichment_comp.
    - exact (λ _ _ f, enriched_profunctor_collage_enrichment_from_arr f).
    - exact (λ _ _ f, enriched_profunctor_collage_enrichment_to_arr f).
  Defined.

  Proposition enriched_profunctor_collage_enrichment_laws
    : enrichment_laws
        enriched_profunctor_collage_enrichment_data.
  Proof.
    repeat split.
    - intros x₁ x₂.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        cbn in *.
      + apply enrichment_id_left.
      + use arrow_from_tensor_initial_l_benabou_cosmos_eq.
      + rewrite rmap_e_id.
        apply idpath.
      + apply enrichment_id_left.
    - intros x₁ x₂.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        cbn in *.
      + apply enrichment_id_right.
      + use arrow_from_tensor_initial_r_benabou_cosmos_eq.
      + rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        rewrite lmap_e_id.
        rewrite sym_mon_braiding_lunitor.
        apply idpath.
      + apply enrichment_id_right.
    - intros x₁ x₂ x₃ x₄.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        induction x₃ as [ x₃ | y₃ ] ;
        induction x₄ as [ x₄ | y₄ ] ;
        cbn in *.
      + apply enrichment_assoc.
      + use arrow_from_tensor_initial_1_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_2_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_2_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_l_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_1_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_l_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_l_benabou_cosmos_eq.
      + apply rmap_e_comp.
      + use arrow_from_tensor_initial_1_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_2_benabou_cosmos_eq.
      + use arrow_from_tensor_initial_2_benabou_cosmos_eq.
      + etrans.
        {
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite rmap_e_lmap_e.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_comp_id_l.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          rewrite sym_mon_tensor_lassociator'.
          rewrite !assoc'.
          rewrite mon_rassociator_lassociator.
          rewrite id_right.
          rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
          rewrite mon_rassociator_lassociator.
          rewrite id_left.
          rewrite !assoc.
          rewrite sym_mon_braiding_inv.
          rewrite id_left.
          apply idpath.
        }
        apply idpath.
      + use arrow_from_tensor_initial_1_benabou_cosmos_eq.
      + refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          apply maponpaths.
          exact (lmap_e_comp' P y₃ y₂ y₁ x₄).
        }
        rewrite !assoc.

        apply maponpaths_2.
        rewrite tensor_comp_r_id_l.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply sym_mon_tensor_lassociator'.
        }
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite sym_mon_tensor_rassociator.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite mon_rassociator_lassociator.
          rewrite id_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          rewrite id_left.
          apply idpath.
        }
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      + apply enrichment_assoc.
    - intros x₁ x₂ f.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        cbn in *.
      + apply enriched_to_from_arr.
      + apply idpath.
      + apply idpath.
      + apply enriched_to_from_arr.
    - intros x₁ x₂ f.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        cbn in *.
      + apply enriched_from_to_arr.
      + apply idpath.
      + apply idpath.
      + apply enriched_from_to_arr.
    - intros x.
      induction x as [ x | y ] ; cbn in *.
      + apply enriched_to_arr_id.
      + apply enriched_to_arr_id.
    - intros x₁ x₂ x₃ f g.
      induction x₁ as [ x₁ | y₁ ] ;
        induction x₂ as [ x₂ | y₂ ] ;
        induction x₃ as [ x₃ | y₃ ] ;
        cbn in *.
      + exact (enriched_to_arr_comp E₁ f g).
      + rewrite tensor_split'.
        rewrite !assoc.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite <- tensor_rinvunitor.
        refine (!(id_right _) @ _).
        rewrite !assoc'.
        apply maponpaths.
        apply InitialArrowEq.
      + apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        refine (!(id_right _) @ _).
        rewrite !assoc'.
        apply maponpaths.
        apply InitialArrowEq.
      + rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        refine (!(id_right _) @ _).
        rewrite !assoc'.
        apply maponpaths.
        apply InitialArrowEq.
      + rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply idpath.
      + apply maponpaths.
        rewrite tensor_split'.
        rewrite !assoc.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite <- tensor_rinvunitor.
        refine (!(id_right _) @ _).
        rewrite !assoc'.
        apply maponpaths.
        apply InitialArrowEq.
      + rewrite tensor_split'.
        rewrite !assoc.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite <- tensor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        unfold lmap_e_arr.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        rewrite sym_mon_braiding_rinvunitor.
        apply idpath.
      + exact (enriched_to_arr_comp E₂ f g).
  Qed.

  Definition enriched_profunctor_collage_enrichment
    : enrichment enriched_profunctor_collage_precategory_data V.
  Proof.
    simple refine (_ ,, _).
    - exact enriched_profunctor_collage_enrichment_data.
    - exact enriched_profunctor_collage_enrichment_laws.
  Defined.

  (** * 3. The underlying category *)
  Proposition enriched_profunctor_collage_is_precategory
    : is_precategory enriched_profunctor_collage_precategory_data.
  Proof.
    exact (is_precategory_from_enrichment
             enriched_profunctor_collage_enrichment).
  Qed.

  Proposition enriched_profunctor_collage_homsets
    : has_homsets enriched_profunctor_collage_precategory_ob_mor.
  Proof.
    intros x₁ x₂.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ] ;
      cbn ;
      apply homset_property.
  Qed.

  Definition enriched_profunctor_collage_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact enriched_profunctor_collage_precategory_data.
    - exact enriched_profunctor_collage_is_precategory.
  Defined.

  Definition enriched_profunctor_collage
    : category.
  Proof.
    use make_category.
    - exact enriched_profunctor_collage_precategory.
    - exact enriched_profunctor_collage_homsets.
  Defined.

  (** * 4. The underlying category is univalent *)
  Definition idtoiso_in_enriched_collage_inl
             {x₁ x₂ : C₁}
             (p : x₁ = x₂)
    : pr1 (idtoiso p)
      =
      pr1 (@idtoiso
             enriched_profunctor_collage
             (inl x₁)
             (inl x₂)
             (maponpaths inl p)).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition idtoiso_in_enriched_collage_inr
             {x₁ x₂ : C₂}
             (p : x₁ = x₂)
    : pr1 (idtoiso p)
      =
      pr1 (@idtoiso
             enriched_profunctor_collage
             (inr x₁)
             (inr x₂)
             (maponpaths inr p)).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition is_univalent_enriched_profunctor_collage
              (H₁ : is_univalent C₁)
              (H₂ : is_univalent C₂)
              (HV : (I_{V} --> IV) → ∅)
    : is_univalent enriched_profunctor_collage.
  Proof.
    intros x₁ x₂.
    induction x₁ as [ x₁ | y₁ ] ;
      induction x₂ as [ x₂ | y₂ ].
    - use weqhomot.
      + exact (make_weq _ (H₁ _ _) ∘ paths_inl_inl_equiv _ _)%weq.
      + intro p ; cbn -[equality_by_case_equiv].
        use z_iso_eq.
        refine (idtoiso_in_enriched_collage_inl (paths_inl_inl_equiv x₁ x₂ p) @ _).
        do 2 apply maponpaths.
        apply (homotinvweqweq (paths_inl_inl_equiv _ _)).
    - use weqhomot.
      + refine (invweq _ ∘ paths_inl_inr_equiv _ _)%weq.
        use weqtoempty.
        intro f.
        use HV.
        exact f.
      + intro p.
        use fromempty.
        exact (negpathsii1ii2 _ _ p).
    - use weqhomot.
      + refine (invweq _ ∘ paths_inr_inl_equiv _ _)%weq.
        use weqtoempty.
        intro f.
        use HV.
        exact (inv_from_z_iso f).
      + intro p.
        use fromempty.
        exact (negpathsii2ii1 _ _ p).
    - use weqhomot.
      + exact (make_weq _ (H₂ _ _) ∘ paths_inr_inr_equiv _ _)%weq.
      + intro p ; cbn -[equality_by_case_equiv].
        use z_iso_eq.
        refine (idtoiso_in_enriched_collage_inr (paths_inr_inr_equiv y₁ y₂ p) @ _).
        do 2 apply maponpaths.
        apply (homotinvweqweq (paths_inr_inr_equiv _ _)).
  Qed.

  (** * 5. The left inclusion *)
  Definition enriched_profunctor_collage_inl_data
    : functor_data C₁ enriched_profunctor_collage.
  Proof.
    use make_functor_data.
    - exact (λ x, inl x).
    - exact (λ x₁ x₂ f, f).
  Defined.

  Proposition enriched_profunctor_collage_inl_laws
    : is_functor enriched_profunctor_collage_inl_data.
  Proof.
    split ; intro ; intros ; apply idpath.
  Qed.

  Definition enriched_profunctor_collage_inl
    : C₁ ⟶ enriched_profunctor_collage.
  Proof.
    use make_functor.
    - exact enriched_profunctor_collage_inl_data.
    - exact enriched_profunctor_collage_inl_laws.
  Defined.

  Definition enriched_profunctor_collage_inl_enrichment
    : functor_enrichment
        enriched_profunctor_collage_inl
        E₁
        enriched_profunctor_collage_enrichment.
  Proof.
    refine ((λ x₁ x₂, identity _) ,, _).
    abstract
      (repeat split ;
       intro ; intros ;
       cbn ;
       rewrite ?tensor_id_id ;
       rewrite ?id_left, !id_right ;
       apply idpath).
  Defined.

  Definition enriched_profunctor_collage_inl_ff
    : fully_faithful_enriched_functor
        enriched_profunctor_collage_inl_enrichment.
  Proof.
    intros x₁ x₂.
    apply is_z_isomorphism_identity.
  Defined.

  (** * 6. The right inclusion *)
  Definition enriched_profunctor_collage_inr_data
    : functor_data C₂ enriched_profunctor_collage.
  Proof.
    use make_functor_data.
    - exact (λ x, inr x).
    - exact (λ x₁ x₂ f, f).
  Defined.

  Proposition enriched_profunctor_collage_inr_laws
    : is_functor enriched_profunctor_collage_inr_data.
  Proof.
    split ; intro ; intros ; apply idpath.
  Qed.

  Definition enriched_profunctor_collage_inr
    : C₂ ⟶ enriched_profunctor_collage.
  Proof.
    use make_functor.
    - exact enriched_profunctor_collage_inr_data.
    - exact enriched_profunctor_collage_inr_laws.
  Defined.

  Definition enriched_profunctor_collage_inr_enrichment
    : functor_enrichment
        enriched_profunctor_collage_inr
        E₂
        enriched_profunctor_collage_enrichment.
  Proof.
    refine ((λ x₁ x₂, identity _) ,, _).
    abstract
      (repeat split ;
       intro ; intros ;
       cbn ;
       rewrite ?tensor_id_id ;
       rewrite ?id_left, !id_right ;
       apply idpath).
  Defined.

  Definition enriched_profunctor_collage_inr_ff
    : fully_faithful_enriched_functor
        enriched_profunctor_collage_inr_enrichment.
  Proof.
    intros x₁ x₂.
    apply is_z_isomorphism_identity.
  Defined.

  (** * 7. The square of the collage *)
  Definition enriched_profunctor_collage_square
    : enriched_profunctor_square
        enriched_profunctor_collage_inl_enrichment
        enriched_profunctor_collage_inr_enrichment
        P
        (identity_enriched_profunctor _).
  Proof.
    use make_enriched_profunctor_transformation.
    - exact (λ _ _, identity _).
    - split.
      + abstract
          (intros ; cbn ;
           rewrite !tensor_id_id ;
           rewrite !id_left, id_right ;
           rewrite !assoc ;
           rewrite sym_mon_braiding_inv ;
           apply id_left).
      + abstract
          (intros ; cbn ;
           rewrite !tensor_id_id ;
           rewrite !id_left, id_right ;
           apply idpath).
  Defined.
End CollageOfProfunctor.
