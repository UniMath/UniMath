(**********************************************************************

 The category of enriched functors

 We define the category of enriched functors and prove that it gives
 rise to a univalent category. To do so, we use displayed categories.
 The objects of this category are enriched functors and the morphisms
 are enriched natural transformations.

 In addition, we show that there is an enrichment over the functor
 category if the category over which we enriched is a complete monoidal
 closed category.

 To construct this enrichment, we must encode the type of enriched
 natural transformations as an object in the monoidal category `V`. The
 idea behind this encoding is as follows: first of all, an enriched
 transformation consists of a family of morphisms. We encode this by
 taking a suitable product (we call it `P₁` below). Second of all, an
 enriched transformation satisfies a commutativity condition. We encode
 this by taking a suitable equalizer: this means that we look at those
 families of morphisms such that a certain square commutes. We do so
 by first defining the product `P₂` (note that we take a product over
 pairs of objects in `C₁`). As such, we must construct two morphisms
 from `P₁` to `P₂`. Each of these represents one side of the naturality
 square.

 It is important to note that in the definition of `P₂`, we make use of
 the fact that the monoidal category `V` is closed. The encoded
 condition relates to the usual condition of V-naturality by
 adjointness.

 One might think that one could also use ends (as defined in
 Limits.Ends) to construct the required object. However, this is not
 the case. If one would do so, then only gets natural transformations
 that ar not necessarily enriched. This would thus not give  the right
 morphisms in the category.

 Contents
 1. The category of enriched functors
 2. This category is univalent
 3. Operations on the enriched functor category
 4. The enrichment
 5. Enrichment for enriched presheaf categories

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.HomFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedFunctorCategory.
  Context {V : monoidal_cat}
          {C₁ C₂ : category}
          (E₁ : enrichment C₁ V)
          (E₂ : enrichment C₂ V).

  Definition functor_enrichment_disp_cat_ob_mor
    : disp_cat_ob_mor [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact (λ F, functor_enrichment F E₁ E₂).
    - exact (λ F₁ F₂ FE₁ FE₂ α, nat_trans_enrichment (pr1 α) FE₁ FE₂).
  Defined.

  Definition functor_enrichment_disp_cat_id_comp
    : disp_cat_id_comp [C₁, C₂] functor_enrichment_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ F FE, id_trans_enrichment FE).
    - exact (λ F₁ F₂ F₃ τ θ FE₁ FE₂ FE₃ τE θE, comp_trans_enrichment τE θE).
  Defined.

  Definition functor_enrichment_disp_cat_data
    : disp_cat_data [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact functor_enrichment_disp_cat_ob_mor.
    - exact functor_enrichment_disp_cat_id_comp.
  Defined.

  Definition functor_enrichment_disp_cat
    : disp_cat [C₁ , C₂].
  Proof.
    simple refine (_ ,, _).
    - exact functor_enrichment_disp_cat_data.
    - abstract
        (repeat split ;
         intro ; intros ;
         try (apply isaprop_nat_trans_enrichment) ;
         apply isasetaprop ;
         apply isaprop_nat_trans_enrichment).
  Defined.

  Definition is_univalent_disp_functor_enrichment_disp_cat
    : is_univalent_disp functor_enrichment_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros F FE₁ FE₂.
    use isweqimplimpl.
    - cbn in * ; intro τ.
      use subtypePath.
      {
        intro.
        apply isaprop_is_functor_enrichment.
      }
      use funextsec ; intro x.
      use funextsec ; intro y.
      pose (p := pr1 τ x y).
      cbn in p.
      rewrite !enriched_from_arr_id in p.
      refine (_ @ !p @ _) ; clear p.
      + rewrite <- !(functor_enrichment_id FE₁).
        rewrite (tensor_comp_r_id_l _ _ (FE₁ x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp FE₁).
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          exact (enrichment_id_left E₁ x y).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_linvunitor_lunitor.
        }
        apply id_left.
      + rewrite <- !(functor_enrichment_id FE₂).
        rewrite (tensor_comp_l_id_l (FE₂ x y)).
        rewrite !assoc'.
        rewrite <- (functor_enrichment_comp FE₂).
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          exact (enrichment_id_right E₁ x y).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
    - apply isaset_functor_enrichment.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_nat_trans_enrichment.
  Qed.

  (**
   1. The category of enriched functors
   *)
  Definition enriched_functor_category
    : category
    := total_category functor_enrichment_disp_cat.

  (**
   2. This category is univalent
   *)
  Definition is_univalent_enriched_functor_cat
             (HC₂ : is_univalent C₂)
    : is_univalent enriched_functor_category.
  Proof.
    use is_univalent_total_category.
    - use is_univalent_functor_category.
      exact HC₂.
    - exact is_univalent_disp_functor_enrichment_disp_cat.
  Defined.
End EnrichedFunctorCategory.

Definition enriched_univalent_functor_category
           {V : monoidal_cat}
           (C₁ C₂ : univalent_category)
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : univalent_category
  := enriched_functor_category E₁ E₂ ,, is_univalent_enriched_functor_cat _ _ (pr2 C₂).

(**
 3. Operations on the enriched functor category
 *)
Definition is_nat_z_iso_enriched_functor_category_z_iso
           {V : monoidal_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {F G : enriched_functor_category E₁ E₂}
           (τ : z_iso F G)
  : is_nat_z_iso (pr111 τ).
Proof.
  exact (pr2 (nat_z_iso_from_z_iso _ (z_iso_base_from_total τ))).
Defined.

Definition comp_enriched_functor_category
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_functor_category E₁ E₂)
           (G : enriched_functor_category E₂ E₃)
  : enriched_functor_category E₁ E₃
  := pr1 F ∙ pr1 G
     ,,
     functor_comp_enrichment (pr2 F) (pr2 G).

Definition pre_whisker_enriched_functor_category
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_functor_category E₁ E₂)
           {G₁ G₂ : enriched_functor_category E₂ E₃}
           (τ : G₁ --> G₂)
  : comp_enriched_functor_category F G₁
    -->
    comp_enriched_functor_category F G₂.
Proof.
  simple refine (_ ,, _).
  - exact (pre_whisker (pr11 F) (pr1 τ)).
  - use pre_whisker_enrichment.
    exact (pr2 τ).
Defined.

Definition post_whisker_enriched_functor_category
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F₁ F₂ : enriched_functor_category E₁ E₂}
           (τ : F₁ --> F₂)
           (G : enriched_functor_category E₂ E₃)
  : comp_enriched_functor_category F₁ G
    -->
    comp_enriched_functor_category F₂ G.
Proof.
  simple refine (_ ,, _).
  - exact (post_whisker (pr1 τ) (pr1 G)).
  - use post_whisker_enrichment.
    exact (pr2 τ).
Defined.

Definition lassociator_enriched_functor_category
           {V : monoidal_cat}
           {C₁ C₂ C₃ C₄ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {E₄ : enrichment C₄ V}
           (F : enriched_functor_category E₁ E₂)
           (G : enriched_functor_category E₂ E₃)
           (H : enriched_functor_category E₃ E₄)
  : comp_enriched_functor_category (comp_enriched_functor_category F G) H
    -->
    comp_enriched_functor_category F (comp_enriched_functor_category G H)
  := nat_trans_id _ ,, lassociator_enrichment (pr2 F) (pr2 G) (pr2 H).

Definition rassociator_enriched_functor_category
           {V : monoidal_cat}
           {C₁ C₂ C₃ C₄ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {E₄ : enrichment C₄ V}
           (F : enriched_functor_category E₁ E₂)
           (G : enriched_functor_category E₂ E₃)
           (H : enriched_functor_category E₃ E₄)
  : comp_enriched_functor_category F (comp_enriched_functor_category G H)
    -->
    comp_enriched_functor_category (comp_enriched_functor_category F G) H
  := nat_trans_id _ ,, rassociator_enrichment (pr2 F) (pr2 G) (pr2 H).

(**
 4. The enrichment
 *)
Section EnrichedFunctorCategory.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          (E₁ : enrichment C₁ V)
          (E₂ : enrichment C₂ V)
          (EqV : Equalizers V)
          (PV : Products C₁ V)
          (PV' : Products (C₁ × C₁) V).

  Definition hom_functor_on_functors
             (F G : C₁ ⟶ C₂)
    : category_binproduct (C₁^opp) C₁ ⟶ V
    := pair_functor (functor_op F) G ∙ enriched_hom_functor E₂.

  Section FunctorEnrichmentConstruction.
    Context {F G : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
            (EG : functor_enrichment G E₁ E₂).

    Let P₁ : Product C₁ V (λ x, E₂ ⦃ F x, G x ⦄)
      := PV (λ x, E₂ ⦃ F x , G x ⦄).

    Let P₂ : Product
               (C₁ × C₁)
               V
               (λ xy, (E₁ ⦃ pr1 xy, pr2 xy ⦄) ⊸ (E₂ ⦃ F (pr1 xy), G (pr2 xy) ⦄))
      := PV' (λ xy, E₁ ⦃ pr1 xy , pr2 xy ⦄ ⊸ (E₂ ⦃ F (pr1 xy) , G (pr2 xy) ⦄)).

    Definition enriched_functor_left_map_ob
               (x y : C₁)
      : E₂ ⦃ F x , G x ⦄ --> (E₁ ⦃ x, y ⦄) ⊸ (E₂ ⦃ F x , G y ⦄).
    Proof.
      use internal_lam.
      exact (sym_mon_braiding _ _ _
             · (EG _ _ #⊗ identity _)
             · enriched_comp _ _ _ _).
    Defined.

    Let σ : ∏ (x y : C₁), E₂ ⦃ F x , G x ⦄ --> (E₁ ⦃ x, y ⦄) ⊸ (E₂ ⦃ F x , G y ⦄)
      := enriched_functor_left_map_ob.

    Definition enriched_functor_right_map_ob
               (x y : C₁)
      : E₂ ⦃ F y , G y ⦄ --> (E₁ ⦃ x, y ⦄) ⊸ (E₂ ⦃ F x , G y ⦄).
    Proof.
      use internal_lam.
      exact ((identity _ #⊗ EF _ _)
             · enriched_comp _ _ _ _).
    Defined.

    Let ρ : ∏ (x y : C₁), E₂ ⦃ F y , G y ⦄ --> (E₁ ⦃ x, y ⦄) ⊸ (E₂ ⦃ F x , G y ⦄)
      := enriched_functor_right_map_ob.

    Definition enriched_functor_left_map
      : P₁ --> P₂.
    Proof.
      use ProductArrow.
      exact (λ xy, ProductPr _ _ _ (pr1 xy) · σ (pr1 xy) (pr2 xy)).
    Defined.

    Definition enriched_functor_right_map
      : P₁ --> P₂.
    Proof.
      use ProductArrow.
      exact (λ xy, ProductPr _ _ _ (pr2 xy) · ρ (pr1 xy) (pr2 xy)).
    Defined.

    Definition enriched_functor_hom
      : Equalizer enriched_functor_left_map enriched_functor_right_map
      := EqV _ _ enriched_functor_left_map enriched_functor_right_map.

    Definition enriched_functor_hom_pr
               (i : C₁)
      : enriched_functor_hom --> E₂ ⦃ F i, G i ⦄
      := EqualizerArrow _ · ProductPr _ _ _ i.

    Definition enriched_functor_hom_eq
               (i j : C₁)
      : enriched_functor_hom_pr i · σ i j
        =
        enriched_functor_hom_pr j · ρ i j.
    Proof.
      pose (maponpaths
              (λ z, z · ProductPr _ _ _ (i ,, j))
              (EqualizerEqAr enriched_functor_hom))
        as p.
      cbn in p.
      unfold enriched_functor_left_map in p.
      unfold enriched_functor_right_map in p.
      rewrite !assoc' in p.
      rewrite !(ProductPrCommutes _ _ _ P₂ _ _ (i ,, j)) in p.
      rewrite !assoc in p.
      exact p.
    Qed.

    Definition enriched_functor_hom_eq'
               (x y : C₁)
      : sym_mon_braiding V  _ _
        · (EG x y #⊗ enriched_functor_hom_pr x · enriched_comp E₂ (F x) (G x) (G y))
        =
        enriched_functor_hom_pr y #⊗ EF x y
        · enriched_comp E₂ (F x) (F y) (G y).
    Proof.
      pose (maponpaths
              (λ z, z #⊗ identity _ · internal_eval _ _)
              (enriched_functor_hom_eq x y))
        as p.
      cbn in p.
      rewrite !tensor_comp_r_id_r in p.
      unfold σ, ρ in p.
      unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob in p.
      rewrite !assoc' in p.
      rewrite !internal_beta in p.
      rewrite !assoc in p.
      rewrite tensor_sym_mon_braiding in p.
      rewrite <- tensor_split' in p.
      rewrite !assoc' in p.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) in p.
      rewrite <- tensor_split in p.
      exact p.
    Qed.

    Definition mor_to_enriched_functor_hom
               {v : V}
               (fv : ∏ (i : C₁) , v --> E₂ ⦃ F i, G i ⦄)
               (p : ∏ (x y : C₁), fv x · σ x y = fv y · ρ x y)
      : v --> enriched_functor_hom.
    Proof.
      use EqualizerIn.
      - use ProductArrow.
        exact fv.
      - abstract
          (use ProductArrow_eq ;
           intros xy ;
           unfold enriched_functor_left_map ;
           unfold enriched_functor_right_map ;
           rewrite !assoc' ;
           rewrite !(ProductPrCommutes _ _ _ P₂) ;
           rewrite !assoc ;
           rewrite !(ProductPrCommutes _ _ _ P₁) ;
           apply p).
    Defined.

    Proposition mor_to_enriched_functor_hom_pr
                {v : V}
                (fv : ∏ (i : C₁) , v --> E₂ ⦃ F i, G i ⦄)
                (p : ∏ (x y : C₁), fv x · σ x y = fv y · ρ x y)
                (i : C₁)
      : mor_to_enriched_functor_hom fv p · enriched_functor_hom_pr i
        =
        fv i.
    Proof.
      unfold mor_to_enriched_functor_hom, enriched_functor_hom_pr.
      rewrite !assoc.
      rewrite EqualizerCommutes.
      apply (ProductPrCommutes _ _ _ P₁).
    Qed.

    Definition mor_to_enriched_functor_unique
               {v : V}
               (f g : v --> enriched_functor_hom)
               (p : ∏ (x : C₁), f · enriched_functor_hom_pr x
                                =
                                g · enriched_functor_hom_pr  x)
      : f = g.
    Proof.
      use EqualizerInsEq.
      use ProductArrow_eq.
      intro x.
      rewrite !assoc'.
      exact (p x).
    Defined.
  End FunctorEnrichmentConstruction.

  Section EnrichmentIdentity.
    Context {F : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂).

    Proposition enriched_functor_hom_id_eq
                (x y : C₁)
      : enriched_id E₂ (F x) · enriched_functor_left_map_ob EF x y
        =
        enriched_id E₂ (F y) · enriched_functor_right_map_ob EF x y.
    Proof.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob.
      rewrite !assoc'.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        apply idpath.
      }
      rewrite tensor_lunitor.
      rewrite tensor_runitor.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite sym_mon_braiding_runitor.
      apply idpath.
    Qed.

    Definition enriched_functor_hom_id
      : I_{V} --> enriched_functor_hom EF EF.
    Proof.
      use mor_to_enriched_functor_hom.
      - exact (λ x, enriched_id E₂ (F x)).
      - exact enriched_functor_hom_id_eq.
    Defined.

    Proposition enriched_functor_hom_id_comm
                (x : C₁)
      : enriched_functor_hom_id · enriched_functor_hom_pr EF EF x
        =
        enriched_id E₂ (F x).
    Proof.
      exact (mor_to_enriched_functor_hom_pr
               EF EF
               _
               _
               x).
    Qed.
  End EnrichmentIdentity.

  Section EnrichmentComp.
    Context {F G H : C₁ ⟶ C₂}
            (EF : functor_enrichment F E₁ E₂)
            (EG : functor_enrichment G E₁ E₂)
            (EH : functor_enrichment H E₁ E₂).

    Definition enriched_functor_hom_comp_data
               (x : C₁)
      : enriched_functor_hom EG EH ⊗ enriched_functor_hom EF EG
        -->
        E₂ ⦃ F x , H x ⦄
      := enriched_functor_hom_pr EG EH x #⊗ enriched_functor_hom_pr EF EG x
         · enriched_comp _ _ _ _.

    Proposition enriched_functor_hom_comp_laws
                (x y : C₁)
      : enriched_functor_hom_comp_data x · enriched_functor_left_map_ob EH x y
        =
        enriched_functor_hom_comp_data y · enriched_functor_right_map_ob EF x y.
    Proof.
      unfold enriched_functor_hom_comp_data.
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob.
      rewrite !assoc'.
      rewrite !internal_beta.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_sym_mon_braiding.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        apply idpath.
      }
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite tensor_rassociator.
          apply idpath.
        }
        rewrite !assoc.
        do 4 apply maponpaths_2.
        refine (!(id_left _) @ _).
        rewrite <- mon_lassociator_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply sym_mon_hexagon_rassociator.
      }
      etrans.
      {
        rewrite !assoc'.
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_mor.
        rewrite !id_left.
        rewrite !id_right.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_right.
          rewrite tensor_comp_r_id_l.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        exact (enriched_functor_hom_eq' EG EH x y).
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite tensor_lassociator.
        rewrite !assoc.
        rewrite tensor_lassociator.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite id_right.
        rewrite <- tensor_comp_id_l.
        rewrite <- !tensor_comp_mor.
        rewrite id_left, id_right.
        apply maponpaths_2.
        apply maponpaths.
        rewrite tensor_split'.
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        rewrite <- tensor_split.
        exact (enriched_functor_hom_eq' EF EG x y).
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_comp_l_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite id_left.
        rewrite <- tensor_lassociator.
        rewrite !assoc'.
        rewrite mon_lassociator_rassociator.
        rewrite id_right.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite <- tensor_split'.
      rewrite <- !tensor_comp_mor.
      rewrite id_right.
      apply idpath.
    Qed.

    Definition enriched_functor_hom_comp
      : enriched_functor_hom EG EH ⊗ enriched_functor_hom EF EG
        -->
        enriched_functor_hom EF EH.
    Proof.
      use mor_to_enriched_functor_hom.
      - exact enriched_functor_hom_comp_data.
      - exact enriched_functor_hom_comp_laws.
    Defined.

    Proposition enriched_functor_hom_comp_comm
                (x : C₁)
      : enriched_functor_hom_comp
        · enriched_functor_hom_pr EF EH x
        =
        (enriched_functor_hom_pr EG EH x
         #⊗
         enriched_functor_hom_pr EF EG x)
        · enriched_comp E₂ (F x) (G x) (H x).
    Proof.
      unfold enriched_functor_hom_comp.
      rewrite mor_to_enriched_functor_hom_pr.
      apply idpath.
    Qed.
  End EnrichmentComp.

  Section EnrichmentFromArr.
    Context {F G : C₁ ⟶ C₂}
            {τ : F ⟹ G}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (Eτ : nat_trans_enrichment τ EF EG).

    Proposition enriched_functor_hom_from_arr_eq
                (x y : C₁)
      : enriched_from_arr E₂ (τ x) · enriched_functor_left_map_ob EG x y
        =
        enriched_from_arr E₂ (τ y) · enriched_functor_right_map_ob EF x y.
    Proof.
      pose (p := Eτ x y).
      use internal_funext.
      intros a h.
      rewrite !tensor_comp_r_id_r.
      unfold enriched_functor_left_map_ob, enriched_functor_right_map_ob.
      rewrite !assoc'.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!(id_left _) @ _).
        rewrite <- mon_runitor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        exact p.
      }
      clear p.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite sym_mon_braiding_runitor.
      rewrite mon_lunitor_linvunitor.
      rewrite id_left.
      rewrite <- tensor_split'.
      apply idpath.
    Qed.

    Definition enriched_functor_hom_from_arr
      : I_{V} --> enriched_functor_hom EF EG.
    Proof.
      use mor_to_enriched_functor_hom.
      - exact (λ x, enriched_from_arr E₂ (τ x)).
      - exact enriched_functor_hom_from_arr_eq.
    Defined.

    Proposition enriched_functor_hom_from_arr_comm
                (x : C₁)
      : enriched_functor_hom_from_arr
        · enriched_functor_hom_pr EF EG x
        =
        enriched_from_arr E₂ (τ x).
    Proof.
      unfold enriched_functor_hom_from_arr.
      rewrite mor_to_enriched_functor_hom_pr.
      apply idpath.
    Qed.
  End EnrichmentFromArr.

  Section EnrichmentToArr.
    Context {F G : C₁ ⟶ C₂}
            {EF : functor_enrichment F E₁ E₂}
            {EG : functor_enrichment G E₁ E₂}
            (τ : I_{V} --> enriched_functor_hom EF EG).

    Definition enrichment_functor_hom_to_arr_data
      : nat_trans_data F G
      := λ x, enriched_to_arr E₂ (τ · enriched_functor_hom_pr EF EG x).

    Proposition enrichment_functor_hom_to_arr_enrichment
      : nat_trans_enrichment enrichment_functor_hom_to_arr_data EF EG.
    Proof.
      unfold enrichment_functor_hom_to_arr_data.
      intros x y ; cbn.
      rewrite !enriched_from_to_arr.
      rewrite tensor_comp_r_id_l.
      rewrite tensor_comp_l_id_l.
      pose (enriched_functor_hom_eq' EF EG x y) as p.
      rewrite !assoc'.
      rewrite <- p.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite sym_mon_braiding_linvunitor.
      apply idpath.
    Qed.

    Definition enrichment_functor_hom_to_arr
      : F ⟹ G.
    Proof.
      use make_nat_trans.
      - exact enrichment_functor_hom_to_arr_data.
      - exact (is_nat_trans_from_enrichment enrichment_functor_hom_to_arr_enrichment).
    Defined.
  End EnrichmentToArr.

  Definition enriched_functor_category_enrichment_data
    : enrichment_data (enriched_functor_category E₁ E₂) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ F G, enriched_functor_hom (pr2 F) (pr2 G)).
    - exact (λ F, enriched_functor_hom_id (pr2 F)).
    - exact (λ F G H, enriched_functor_hom_comp (pr2 F) (pr2 G) (pr2 H)).
    - exact (λ F G τ, enriched_functor_hom_from_arr (pr2 τ)).
    - exact (λ F G τ,
             enrichment_functor_hom_to_arr τ
             ,,
             enrichment_functor_hom_to_arr_enrichment τ).
  Defined.

  Proposition enriched_functor_category_enrichment_laws
    : enrichment_laws enriched_functor_category_enrichment_data.
  Proof.
    repeat split.
    - intros F G.
      use mor_to_enriched_functor_unique.
      intro x ; cbn.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply enriched_functor_hom_id_comm.
      }
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- tensor_lunitor.
      apply maponpaths.
      refine (!_).
      apply enrichment_id_left.
    - intros F G.
      use mor_to_enriched_functor_unique.
      intro x ; cbn.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply enriched_functor_hom_id_comm.
      }
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite <- tensor_runitor.
      apply maponpaths.
      refine (!_).
      apply enrichment_id_right.
    - intros F₁ F₂ F₃ F₄.
      use mor_to_enriched_functor_unique.
      intro x ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite tensor_comp_r_id_l.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc.
      }
      rewrite !assoc.
      rewrite <- !tensor_comp_mor.
      rewrite id_left, id_right.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- tensor_comp_mor.
      rewrite id_left.
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_comp_comm.
      }
      rewrite !tensor_comp_l_id_r.
      apply idpath.
    - intros F G τ.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      unfold enrichment_functor_hom_to_arr_data.
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_from_arr_comm.
      }
      apply enriched_to_from_arr.
    - intros F G τ.
      use mor_to_enriched_functor_unique.
      intro x ; cbn.
      etrans.
      {
        apply enriched_functor_hom_from_arr_comm.
      }
      cbn.
      apply enriched_from_to_arr.
    - intros F.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      unfold enrichment_functor_hom_to_arr_data.
      etrans.
      {
        apply maponpaths.
        apply enriched_functor_hom_id_comm.
      }
      apply enriched_to_arr_id.
    - intros F G H τ θ.
      use subtypePath.
      {
        intro.
        apply isaprop_nat_trans_enrichment.
      }
      use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      unfold enrichment_functor_hom_to_arr_data.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          apply enriched_functor_hom_comp_comm.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite !enriched_functor_hom_from_arr_comm.
        apply idpath.
      }
      refine (!_).
      apply enriched_to_arr_comp.
  Qed.

  Definition enriched_functor_category_enrichment
    : enrichment (enriched_functor_category E₁ E₂) V
    := enriched_functor_category_enrichment_data
       ,,
       enriched_functor_category_enrichment_laws.
End EnrichedFunctorCategory.

(**
 5. Enrichment for enriched presheaf categories
 *)
Definition enriched_presheaf_enrichment
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
           (EqV : Equalizers V)
           (PV : Products C V)
           (PV' : Products (C × C) V)
  : enrichment
      (enriched_functor_category
         (op_enrichment V E)
         (self_enrichment V))
      V
  := enriched_functor_category_enrichment
       (op_enrichment V E)
       (self_enrichment V)
       EqV
       PV
       PV'.
