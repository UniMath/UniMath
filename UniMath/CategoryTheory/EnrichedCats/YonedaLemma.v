(*************************************************************************

 The Yoneda lemma for enriched categories

 We prove the Yoneda lemma for enriched categories.

 For enriched categories, there are several options for formulating the
 Yoneda lemma. First of all, one could look at the weak Yoneda lemma. The
 weak Yoneda lemma says something about the *set* of natural transformations,
 namely that this section is isomorphic to the collection of global
 elements. This statement is proven in Section 1.9 of [1].

 Alternatively, one could truly use the enrichments. Instead of talking
 about the set of natural transformations, one talks about the object in
 the category `V` over which we enrich. The existence of this object
 relies on `V` being a symmetric closed monoidal category with enough
 limits. This statement is called the strong Yoneda Lemma, and it is
 proven in Section 2.4 of [1].

 In this file, we prove the strong Yoneda lemma. The precise formulation
 that we use, is that the Yoneda embedding is a fully faithful enriched
 functor.

 The main challenge in the proof is applying the naturality. In the strong
 Yoneda lemma, we are working with an object in `V` that represents the
 enriched natural transformations. This object is defined when constructing
 the enriched functor category (see Examples.FunctorCategory.v). Concretely,
 we take an equalizer (represents the naturality condition) of a product
 (the morphisms of the natural transformation). To use the naturality, we
 need to use the fact that the equalizer gives rise to an equalizer diagram.
 This comes up in the statement [yoneda_inv_left].

 References
 [1]: Basic Concepts of Enriched Category Theory, Max Kelly
      (http://www.tac.mta.ca/tac/reprints/articles/10/tr10.pdf)

 Contents
 1. The inverse of the Yoneda embedding
 2. The strong Yoneda lemma

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FunctorCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Yoneda.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section YonedaLemma.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (EqV : Equalizers V)
          (PV : Products C V)
          (PV' : Products (C × C) V).

  (** * 1. The inverse of the Yoneda embedding *)
  Section Inverse.
    Context (x y : C).

    Definition yoneda_inv
      : enriched_presheaf_enrichment E EqV PV PV'
          ⦃ enriched_yoneda_functor E x , enriched_yoneda_functor E y ⦄
        -->
        E ⦃ x, y ⦄
      := EqualizerArrow _
         · ProductPr _ _ _ x
         · mon_rinvunitor _
         · (identity _ #⊗ enriched_id E x)
         · internal_eval (E ⦃ x , x ⦄) (E ⦃ x, y ⦄).

    Arguments yoneda_inv /.

    Proposition yoneda_inv_right
      : enriched_yoneda_enrichment E EqV PV PV' x y · yoneda_inv = identity _.
    Proof.
      cbn.
      rewrite !assoc.
      rewrite EqualizerCommutes.
      etrans.
      {
        do 3 apply maponpaths_2.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      apply mon_rinvunitor_runitor.
    Qed.

    Proposition yoneda_inv_left
      : yoneda_inv · enriched_yoneda_enrichment E EqV PV PV' x y = identity _.
    Proof.
      cbn.
      use EqualizerInsEq.
      rewrite !assoc'.
      rewrite EqualizerCommutes.
      rewrite id_left.
      refine (_ @ id_right _).
      use ProductArrow_eq.
      intro z.
      rewrite !assoc'.
      rewrite id_left.
      etrans.
      {
        do 5 apply maponpaths.
        exact (ProductPrCommutes C V _ _ _ _ _).
      }
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      (* we want to use naturality *)
      pose (EqualizerEqAr
              (enriched_functor_hom
                 (op_enrichment V E)
                 (self_enrichment V)
                 EqV PV PV'
                 (enriched_repr_presheaf_enrichment E x)
                 (enriched_repr_presheaf_enrichment E y)))
        as p₁.
      cbn in p₁.
      unfold enriched_functor_left_map, enriched_functor_right_map in p₁.
      unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob in p₁.
      (* we apply naturality on a morphism going from `x` to `y` *)
      pose (maponpaths
              (λ f, f · ProductPr (C ^opp × C ^opp) V _ (x ,, z))
              p₁ : _ = _) as p₂.
      rewrite !assoc' in p₂.
      pose (!(maponpaths (λ z, _ · z) (ProductPrCommutes (C^opp × C^opp) V _ _ _ _ _))
            @ p₂
            @ maponpaths (λ z, _ · z) (ProductPrCommutes (C^opp × C^opp) V _ _ _ _ _))
        as p₃.
      cbn -[sym_mon_braiding] in p₃.
      pose (maponpaths (λ z, z #⊗ h · internal_eval _ _) p₃) as p.
      cbn -[sym_mon_braiding] in p.
      refine (_
              @ maponpaths
                  (λ f, f · mon_rinvunitor _
                          · (identity _ #⊗ enriched_id E x)
                          · internal_eval _ _)
                  p
                @ _).
      - rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite internal_beta.
        refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_rinvunitor.
          rewrite tensor_comp_id_r.
          rewrite !assoc'.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- tensor_split'.
            rewrite tensor_split.
            rewrite !assoc'.
            unfold internal_comp.
            rewrite internal_beta.
            rewrite !assoc'.
            apply idpath.
          }
          rewrite !assoc.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite tensor_id_id.
          rewrite !assoc.
          rewrite <- tensor_split'.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_id_id.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- mon_rinvunitor_triangle.
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        refine (_ @ id_right _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_rassociator_lassociator.
          apply id_left.
        }
        apply sym_mon_braiding_inv.
      - rewrite !tensor_comp_r_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite internal_beta.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite tensor_comp_id_r.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- tensor_split'.
            rewrite tensor_split.
            rewrite !assoc'.
            unfold internal_comp.
            rewrite internal_beta.
            rewrite <- tensor_id_id.
            rewrite !assoc.
            rewrite tensor_lassociator.
            rewrite !assoc'.
            apply idpath.
          }
          rewrite !assoc.
          rewrite tensor_lassociator.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply maponpaths.
            rewrite <- tensor_split'.
            rewrite tensor_split.
            apply idpath.
          }
          rewrite tensor_comp_id_l.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite internal_beta.
          apply idpath.
        }
        refine (_ @ id_left _).
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          rewrite !assoc'.
          rewrite <- enrichment_id_left.
          apply idpath.
        }
        rewrite sym_mon_braiding_lunitor.
        rewrite <- mon_runitor_triangle.
        refine (_ @ mon_rinvunitor_runitor _).
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        apply id_left.
    Qed.
  End Inverse.

  (** * 2. The strong Yoneda lemma *)
  Proposition fully_faithful_enriched_yoneda
    : fully_faithful_enriched_functor (enriched_yoneda_enrichment E EqV PV PV').
  Proof.
    intros x y.
    use make_is_z_isomorphism.
    - exact (yoneda_inv x y).
    - split.
      + exact (yoneda_inv_right x y).
      + exact (yoneda_inv_left x y).
  Defined.
End YonedaLemma.
