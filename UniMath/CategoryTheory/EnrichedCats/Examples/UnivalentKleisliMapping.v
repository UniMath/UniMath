(****************************************************************************************

 The universal mapping property of the enriched univalent Kleisli category

 In this file, we establish the universal mapping property of the enriched univalent
 Kleisli category. More precisely, we establish the mapping properties that show that
 the bicategory of enriched categories has Kleisli objects.

 The proof in this file is mostly formal. The main idea is as follows:
 - The universal property of the Rezk completion says that it is a left biadjoint to the
   inclusion from univalent categories into categories.
 - Left biadjoints preserve colimits.
 - Kleisli objects are colimits.
 However, we phrase this proof without any mention of bicategories. The reason for that,
 is that the aforementioned left biadjoint requires the existence of a Rezk completion
 that preserves the universe level, and we do not want to add this assumption to the
 formalization.

 The proof closely follows to how the universal mapping property was established for
 ordinary Kleisli categories (see `categories.KleisliCategory.v`). The main difference
 is that in this file, we need to take the enrichment into account. However, as the
 construction is mostly formal, one can deal with that by using suitable composition
 operators (i.e., composition for enriched functors).

 From a technical point, the main difficulty in the proof is that we constantly need
 to move between functor enrichments and objects of the enriched functor category. For
 that reason, there are numerous `Let` statements in this file. Their purposes is solely
 to give a name to objects in the category of enriched functors, so that we can use them
 systematically.

 Finally, note that we assume that the category `V` has equalizers. This is needed,
 because we construct the univalent Kleisli category as a full subcategory of the
 Eilenberg-Moore category. For the enrichment of the Eilenberg-Moore category, we need
 equalizers.

 Contents
 1. Enriched functors from the univalent Kleisli category
 2. Enriched transformations from the univalent Kleisli category
 3. Uniqueness of 2-cells from the univalent Kleisli category

 ****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.categories.KleisliCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.KleisliEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnivalentKleisliEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.RezkCompletion.RezkUniversalProperty.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedKleisliUMP.
  Context {V : monoidal_cat}
          (HV : Equalizers V)
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  Let K : enriched_functor_category E (kleisli_cat_enrichment HV EM)
    := kleisli_incl M ,, kleisli_incl_enrichment HV EM.

  Let K' : enriched_functor_category E (Kleisli_cat_monad_enrichment EM)
    := Left_Kleisli_functor M ,, Left_Kleisli_functor_enrichment EM.

  Let I : enriched_functor_category
            (Kleisli_cat_monad_enrichment EM)
            (kleisli_cat_enrichment HV EM)
    := functor_to_kleisli_cat M
       ,,
       functor_to_kleisli_cat_enrichment HV EM.

  Let θθ : K --> comp_enriched_functor_category K' I
    := functor_to_kleisli_cat_incl_nat_trans M
       ,,
       functor_to_kleisli_incl_nat_trans_enrichment HV EM.

  Let θθi : comp_enriched_functor_category K' I --> K.
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 (nat_z_iso_inv (functor_to_kleisli_cat_incl_nat_z_iso M))).
    - use nat_z_iso_inv_enrichment.
      apply θθ.
  Defined.

  (** * 1. Enriched functors from the univalent Kleisli category *)
  Section FunctorFromUnivalentKleisli.
    Context {C' : univalent_category}
            (E' : enrichment C' V)
            {F : C ⟶ C'}
            (EF : functor_enrichment F E E')
            {γ : M ∙ F ⟹ F}
            (Eγ : nat_trans_enrichment
                    γ
                    (functor_comp_enrichment EM EF)
                    EF)
            (p : ∏ (x : C), # F (η M x) · γ x = identity _)
            (q : ∏ (x : C), γ (M x) · γ x = # F (μ M x) · γ x).

    Let FF : enriched_functor_category E E' := F ,, EF.

    Let LL : enriched_functor_category (Kleisli_cat_monad_enrichment EM) E'
      := functor_from_kleisli_cat_monad M F γ p q
         ,,
         functor_from_kleisli_cat_enrichment EM E' EF Eγ p q.

    Let ττ : comp_enriched_functor_category K' LL --> FF
      := functor_from_kleisli_cat_monad_nat_trans M F γ p q
         ,,
         functor_from_kleisli_cat_monad_nat_trans_enrichment EM E' EF Eγ p q.

    Definition enriched_functor_from_univalent_kleisli_cat
      : enriched_functor_category (kleisli_cat_enrichment HV EM) E'
      := lift_enriched_functor_along
           _
           (essentially_surjective_functor_to_kleisli_cat M)
           (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)
           LL.

    Definition enriched_functor_from_univalent_kleisli_cat_nat_trans
      : comp_enriched_functor_category
          K
          enriched_functor_from_univalent_kleisli_cat
        -->
        FF
      := post_whisker_enriched_functor_category
           θθ
           enriched_functor_from_univalent_kleisli_cat
         · lassociator_enriched_functor_category _ _ _
         · pre_whisker_enriched_functor_category
             _
             (lift_enriched_functor_along_comm
                _
                (essentially_surjective_functor_to_kleisli_cat M)
                (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)
                LL)
         · ττ.

    Definition enriched_functor_from_univalent_kleisli_cat_nat_trans_is_z_iso
      : is_nat_z_iso (pr11 enriched_functor_from_univalent_kleisli_cat_nat_trans).
    Proof.
      use is_nat_z_iso_comp.
      - use is_nat_z_iso_comp.
        + use is_nat_z_iso_comp.
          * use post_whisker_z_iso_is_z_iso.
            exact (pr2 (functor_to_kleisli_cat_incl_nat_z_iso M)).
          * apply is_nat_z_iso_nat_trans_id.
        + use pre_whisker_on_nat_z_iso.
          apply is_nat_z_iso_enriched_functor_category_z_iso.
      - apply functor_from_kleisli_cat_monad_nat_trans_is_z_iso.
    Defined.

    Proposition enriched_functor_from_univalent_kleisli_cat_eq
                (x : C)
      : pr11 enriched_functor_from_univalent_kleisli_cat_nat_trans (M x) · γ x
        =
        # (pr11 enriched_functor_from_univalent_kleisli_cat) (kleisli_nat_trans M x)
        · pr11 enriched_functor_from_univalent_kleisli_cat_nat_trans x.
    Proof.
      cbn -[lift_enriched_functor_along_comm
              enriched_functor_from_univalent_kleisli_cat].
      rewrite !id_right.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (_ @ functor_id (pr1 enriched_functor_from_univalent_kleisli_cat) _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths_2.
        apply id_left.
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (_ @ functor_id (pr1 enriched_functor_from_univalent_kleisli_cat) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        apply id_left.
      }
      pose (nat_trans_ax
              (pr11 (lift_enriched_functor_along_comm
                      _
                      (essentially_surjective_functor_to_kleisli_cat M)
                      (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)
                      LL))
              (M x) x
              (kleisli_monad_nat_trans M x))
        as r.
      refine (_ @ r @ _).
      - apply maponpaths_2.
        refine (maponpaths (λ z, # _ z) _).
        use eq_mor_kleisli_cat.
        cbn.
        rewrite functor_id, id_left.
        apply idpath.
      - apply maponpaths.
        cbn.
        rewrite functor_id, id_left.
        apply idpath.
    Qed.
  End FunctorFromUnivalentKleisli.

  Section NatTransFromUnivalentKleisli.
    Context {C' : univalent_category}
            (E' : enrichment C' V)
            {G₁ G₂ : enriched_functor_category (kleisli_cat_enrichment HV EM) E'}
            (α : comp_enriched_functor_category K G₁
                 -->
                 comp_enriched_functor_category K G₂)
            (p : ∏ (x : C),
                 #(pr11 G₁) (kleisli_nat_trans M x) · pr11 α x
                 =
                   pr11 α (M x) · #(pr11 G₂) (kleisli_nat_trans M x)).

    (** * 2. Enriched transformations from the univalent Kleisli category *)
    Definition enriched_nat_trans_from_univalent_kleisli_cat_help
      : comp_enriched_functor_category
          K'
          (comp_enriched_functor_category I G₁)
        -->
        comp_enriched_functor_category
          K'
          (comp_enriched_functor_category I G₂)
      := rassociator_enriched_functor_category _ _ _
         · post_whisker_enriched_functor_category θθi _
         · α
         · post_whisker_enriched_functor_category θθ _
         · lassociator_enriched_functor_category _ _ _.

    Proposition enriched_nat_trans_from_univalent_kleisli_cat_help_eq
                (x : C)
      : # (functor_to_kleisli_cat M ∙ pr1 G₁) (kleisli_monad_nat_trans M x)
        · pr11 enriched_nat_trans_from_univalent_kleisli_cat_help x
        =
        pr11 enriched_nat_trans_from_univalent_kleisli_cat_help (M x)
        · # (functor_to_kleisli_cat M ∙ pr1 G₂) (kleisli_monad_nat_trans M x).
    Proof.
      refine (_ @ p x @ _).
      - cbn.
        rewrite !assoc.
        rewrite !id_right.
        rewrite <- (functor_comp (pr1 G₁)).
        etrans.
        {
          apply maponpaths.
          refine (_  @ functor_id (pr1 G₂) _).
          apply maponpaths.
          use subtypePath ; [ intro ; apply isapropunit | ].
          use eq_mor_eilenberg_moore.
          apply idpath.
        }
        rewrite id_right.
        apply maponpaths_2.
        apply maponpaths.
        use eq_mor_kleisli_cat.
        cbn.
        rewrite functor_id.
        rewrite id_left, id_right.
        apply idpath.
      - cbn.
        rewrite !assoc'.
        rewrite !id_left.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          refine (_  @ functor_id (pr1 G₁) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        rewrite id_left.
        rewrite <- (functor_comp (pr1 G₂)).
        do 2 apply maponpaths.
        use eq_mor_kleisli_cat.
        cbn.
        rewrite functor_id.
        rewrite !id_left.
        apply idpath.
    Qed.

    Let ζζ : comp_enriched_functor_category I G₁
             -->
             comp_enriched_functor_category I G₂.
    Proof.
      refine (nat_trans_from_kleisli_cat_monad M _ _ ,, _).
      exact (nat_trans_from_kleisli_cat_monad_enrichment
               EM
               _ _ _
               (pr2 enriched_nat_trans_from_univalent_kleisli_cat_help)
               enriched_nat_trans_from_univalent_kleisli_cat_help_eq).
    Defined.

    Definition enriched_nat_trans_from_univalent_kleisli_cat
      : G₁ --> G₂
      := lift_enriched_nat_trans_along
           _
           (essentially_surjective_functor_to_kleisli_cat M)
           (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)
           ζζ.

    Proposition pre_whisker_enriched_nat_trans_from_univalent_kleisli_cat
                (x : C)
      : pr11 (pre_whisker_enriched_functor_category
               K
               enriched_nat_trans_from_univalent_kleisli_cat)
               x
        =
        pr11 α x.
    Proof.
      pose (maponpaths
              (λ z, pr11 z x)
              (lift_enriched_nat_trans_along_comm
                 _
                 (essentially_surjective_functor_to_kleisli_cat M)
                 (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)
                 ζζ))
        as q.
      refine (q @ _).
      cbn.
      rewrite !id_left, !id_right.
      etrans.
      {
        apply maponpaths.
        refine (_  @ functor_id (pr1 G₂) _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (_  @ functor_id (pr1 G₁) _).
        apply maponpaths.
        use eq_mor_kleisli_cat.
        apply idpath.
      }
      apply id_left.
    Qed.

    (** * 3. Uniqueness of 2-cells from the univalent Kleisli category *)
    Proposition enriched_nat_trans_from_univalent_kleisli_cat_unique
                {β₁ β₂ : G₁ --> G₂}
                (q₁ : ∏ (x : C),
                      pr11 (pre_whisker_enriched_functor_category K β₁) x
                      =
                      pr11 α x)
                (q₂ : ∏ (x : C),
                      pr11 (pre_whisker_enriched_functor_category K β₂) x
                      =
                      pr11 α x)
                (x : kleisli_cat M)
      : pr11 β₁ x = pr11 β₂ x.
    Proof.
      enough (β₁ = β₂) as r.
      {
        exact (maponpaths (λ z, pr11 z x) r).
      }
      use (lift_enriched_nat_trans_eq_along
             _
             (essentially_surjective_functor_to_kleisli_cat M)
             (fully_faithful_functor_to_kleisli_cat_enrichment HV EM)).
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use (@nat_trans_from_kleisli_cat_monad_unique
             _ _
             M
             (functor_to_kleisli_cat M ∙ pr1 G₁)
             (functor_to_kleisli_cat M ∙ pr1 G₂)).
      - exact (pr1 enriched_nat_trans_from_univalent_kleisli_cat_help).
      - use nat_trans_eq.
        {
          apply homset_property.
        }
        intro ; cbn.
        refine (q₁ _ @ _).
        refine (!_).
        rewrite id_left, id_right.
        etrans.
        {
          apply maponpaths.
          refine (_  @ functor_id (pr1 G₂) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        refine (id_right _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (_  @ functor_id (pr1 G₁) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        apply id_left.
      - use nat_trans_eq.
        {
          apply homset_property.
        }
        intro ; cbn.
        refine (q₂ _ @ _).
        refine (!_).
        rewrite id_left, id_right.
        etrans.
        {
          apply maponpaths.
          refine (_  @ functor_id (pr1 G₂) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        refine (id_right _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (_  @ functor_id (pr1 G₁) _).
          apply maponpaths.
          use eq_mor_kleisli_cat.
          apply idpath.
        }
        apply id_left.
    Qed.
  End NatTransFromUnivalentKleisli.
End EnrichedKleisliUMP.
