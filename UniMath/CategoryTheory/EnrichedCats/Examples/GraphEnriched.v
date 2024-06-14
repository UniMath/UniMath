(******************************************************************************************

 The graph of enriched profunctors

 Suppose that we have an enriched profunctor `E₁ ↛e E₂`. Its graph is defined to be the
 following category
 - objects consist of `x : E₁`, `y : E₂` and `f : P y x`
 - morphisms from `(x₁ , y₁ , f₁)` to `(x₂ , y₂ , f₂)` are given by morphisms `g : x₁ --> x₂`
   and `h : y₁ --> y₂` making a diagram commute.
 We define this category as a 2-sided displayed category. In addition, we construct an
 enrichment for this category. To do so, we need to assume that the category `V` over which
 we enriched, has binary products and equalizers (in the formalization, we assume that `V`
 is a Benabou cosmos for convenience). Binary products in `V` are used to construct enriching
 objects that have pairs of morphisms in `E₁` and in `E₂`, and we use equalizers to express
 the commutativity requirement.

 Content
 1. The graph of an enriched profunctor
 2. Accessors and builders for objects and morphisms
 3. The enriched hom object
 4. Operations for the enrichment
 5. Laws for the enrichment
 6. The enrichment for the graph
 7. The first projection
 8. The second projection
 9. The square of the graph

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
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
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

#[local] Opaque sym_mon_braiding.

Section GraphOfEnrichedProfunctor.
  Context {V : benabou_cosmos}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : E₁ ↛e E₂).

  (** * 1. The graph of an enriched profunctor *)
  Definition graph_enriched_profunctor_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, I_{V} --> P x y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g,
             h₂ · lmap_e_arr P y₂ f
             =
             h₁ · rmap_e_arr P g x₁).
  Defined.

  Definition graph_enriched_profunctor_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp
        graph_enriched_profunctor_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite lmap_e_arr_id, rmap_e_arr_id.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ p q ; cbn in *.
      rewrite lmap_e_arr_comp, rmap_e_arr_comp.
      rewrite !assoc.
      rewrite q.
      rewrite !assoc'.
      rewrite <- lmap_e_arr_rmap_e_arr.
      rewrite !assoc.
      rewrite p.
      apply idpath.
  Qed.

  Definition graph_enriched_profunctor_twosided_disp_cat_data
    : twosided_disp_cat_data C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact graph_enriched_profunctor_twosided_disp_cat_ob_mor.
    - exact graph_enriched_profunctor_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_graph_enriched_profunctor_disp_mor
             {x₁ x₂ : C₁}
             (f : x₁ --> x₂)
             {y₁ y₂ : C₂}
             (g : y₁ --> y₂)
             (xy₁ : graph_enriched_profunctor_twosided_disp_cat_data y₁ x₁)
             (xy₂ : graph_enriched_profunctor_twosided_disp_cat_data y₂ x₂)
             (fg fg' : xy₁ -->[ g ][ f ] xy₂)
    : fg = fg'.
  Proof.
    apply homset_property.
  Qed.

  Definition graph_enriched_profunctor_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms
        graph_enriched_profunctor_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_graph_enriched_profunctor_disp_mor).
    apply isasetaprop.
    use invproofirrelevance.
    intro ; intro.
    apply homset_property.
  Qed.

  Definition graph_enriched_profunctor_twosided_disp_cat
    : twosided_disp_cat C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact graph_enriched_profunctor_twosided_disp_cat_data.
    - exact graph_enriched_profunctor_twosided_disp_cat_axioms.
  Defined.

  Proposition is_univalent_graph_enriched_profunctor_twosided_disp_cat
    : is_univalent_twosided_disp_cat
        graph_enriched_profunctor_twosided_disp_cat.
  Proof.
    intros x x' y y' p q f g.
    induction p, q ; cbn in *.
    use isweqimplimpl.
    - intros h.
      pose (p := pr1 h) ; cbn in p.
      rewrite lmap_e_arr_id, rmap_e_arr_id in p.
      rewrite !id_right in p.
      exact (!p).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intro ; intros.
        apply isaprop_graph_enriched_profunctor_disp_mor.
  Qed.

  Definition graph_enriched_profunctor
    : category
    := total_twosided_disp_category
         graph_enriched_profunctor_twosided_disp_cat.

  Proposition is_univalent_graph_enriched_profunctor
              (H₁ : is_univalent C₁)
              (H₂ : is_univalent C₂)
    : is_univalent graph_enriched_profunctor.
  Proof.
    use is_univalent_total_twosided_disp_category.
    - exact H₂.
    - exact H₁.
    - exact is_univalent_graph_enriched_profunctor_twosided_disp_cat.
  Defined.

  (** * 2. Accessors and builders for objects and morphisms *)
  Definition graph_enriched_profunctor_ob
    : UU
    := graph_enriched_profunctor.

  Definition graph_enriched_profunctor_ob_pr1
             (xyf : graph_enriched_profunctor)
    : C₂
    := pr1 xyf.

  Definition graph_enriched_profunctor_ob_pr2
             (xyf : graph_enriched_profunctor)
    : C₁
    := pr12 xyf.

  Definition graph_enriched_profunctor_ob_mor
             (xyf : graph_enriched_profunctor)
    : I_{V}
      -->
      P (graph_enriched_profunctor_ob_pr1 xyf) (graph_enriched_profunctor_ob_pr2 xyf)
    := pr22 xyf.

  Definition make_graph_enriched_profunctor_ob
             (y : C₂)
             (x : C₁)
             (f : I_{V} --> P y x)
    : graph_enriched_profunctor_ob
    := y ,, x ,, f.

  Definition graph_enriched_profunctor_mor
             (xyf₁ xyf₂ : graph_enriched_profunctor_ob)
    : UU
    := xyf₁ --> xyf₂.

  Definition graph_enriched_profunctor_mor_pr1
             {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
             (f : graph_enriched_profunctor_mor xyf₁ xyf₂)
    : graph_enriched_profunctor_ob_pr1 xyf₁
      -->
      graph_enriched_profunctor_ob_pr1 xyf₂
    := pr1 f.

  Definition graph_enriched_profunctor_mor_pr2
             {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
             (f : graph_enriched_profunctor_mor xyf₁ xyf₂)
    : graph_enriched_profunctor_ob_pr2 xyf₁
      -->
      graph_enriched_profunctor_ob_pr2 xyf₂
    := pr12 f.

  Proposition graph_enriched_profunctor_mor_eq
              {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
              (f : graph_enriched_profunctor_mor xyf₁ xyf₂)
    : graph_enriched_profunctor_ob_mor xyf₂
      · lmap_e_arr P _ (graph_enriched_profunctor_mor_pr1 f)
      =
      graph_enriched_profunctor_ob_mor xyf₁
      · rmap_e_arr P (graph_enriched_profunctor_mor_pr2 f) _.
  Proof.
    exact (pr22 f).
  Defined.

  Proposition eq_graph_enriched_profunctor_mor
              {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
              {f g : graph_enriched_profunctor_mor xyf₁ xyf₂}
              (r₁ : graph_enriched_profunctor_mor_pr1 f
                    =
                    graph_enriched_profunctor_mor_pr1 g)
              (r₂ : graph_enriched_profunctor_mor_pr2 f
                    =
                    graph_enriched_profunctor_mor_pr2 g)
    : f = g.
  Proof.
    induction f as [ f₁ [ f₂ p ]].
    induction g as [ g₁ [ g₂ q ]].
    cbn in *.
    induction r₁, r₂ ; cbn.
    do 2 apply maponpaths.
    apply homset_property.
  Qed.

  Definition make_graph_enriched_profunctor_mor
             {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
             (h₁ : graph_enriched_profunctor_ob_pr1 xyf₁
                   -->
                   graph_enriched_profunctor_ob_pr1 xyf₂)
             (h₂ : graph_enriched_profunctor_ob_pr2 xyf₁
                   -->
                   graph_enriched_profunctor_ob_pr2 xyf₂)
             (p : graph_enriched_profunctor_ob_mor xyf₂ · lmap_e_arr P _ h₁
                  =
                  graph_enriched_profunctor_ob_mor xyf₁ · rmap_e_arr P h₂ _)
    : graph_enriched_profunctor_mor xyf₁ xyf₂
    := h₁ ,, h₂ ,, p.

  (** * 3. The enriched hom object *)
  Definition graph_enriched_profunctor_enrichment_hom_prod
             (x₁ x₂ : C₁)
             (y₁ y₂ : C₂)
    : BinProduct _ (E₁ ⦃ x₁ , x₂ ⦄) (E₂ ⦃ y₁ , y₂ ⦄)
    := benabou_cosmos_binproducts V (E₁ ⦃ x₁ , x₂ ⦄) (E₂ ⦃ y₁ , y₂ ⦄).

  Definition graph_enriched_profunctor_enrichment_hom_left
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (f : I_{V} --> P y₁ x₁)
             (g : I_{V} --> P y₂ x₂)
    : graph_enriched_profunctor_enrichment_hom_prod x₁ x₂ y₁ y₂
      -->
      P y₁ x₂
    := BinProductPr1 _ _
       · mon_rinvunitor _
       · (identity _ #⊗ f)
       · rmap_e P y₁ x₁ x₂.

  Definition graph_enriched_profunctor_enrichment_hom_right
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (f : I_{V} --> P y₁ x₁)
             (g : I_{V} --> P y₂ x₂)
    : graph_enriched_profunctor_enrichment_hom_prod x₁ x₂ y₁ y₂
      -->
      P y₁ x₂
    := BinProductPr2 _ _
       · mon_rinvunitor _
       · (identity _ #⊗ g)
       · lmap_e P y₂ y₁ x₂.

  Definition graph_enriched_profunctor_enrichment_hom
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (f : I_{V} --> P y₁ x₁)
             (g : I_{V} --> P y₂ x₂)
    : Equalizer
        (graph_enriched_profunctor_enrichment_hom_left f g)
        (graph_enriched_profunctor_enrichment_hom_right f g)
    := benabou_cosmos_equalizers
         V
         _ _
         (graph_enriched_profunctor_enrichment_hom_left f g)
         (graph_enriched_profunctor_enrichment_hom_right f g).

  Definition graph_enriched_profunctor_enrichment_hom_pr1
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (f : I_{V} --> P y₁ x₁)
             (g : I_{V} --> P y₂ x₂)
    : graph_enriched_profunctor_enrichment_hom f g
      -->
      E₁ ⦃ x₁ , x₂ ⦄
    := EqualizerArrow _ · BinProductPr1 _ _.

  Definition graph_enriched_profunctor_enrichment_hom_pr2
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (f : I_{V} --> P y₁ x₁)
             (g : I_{V} --> P y₂ x₂)
    : graph_enriched_profunctor_enrichment_hom f g
      -->
      E₂ ⦃ y₁ , y₂ ⦄
    := EqualizerArrow _ · BinProductPr2 _ _.

  Proposition graph_enriched_profunctor_enrichment_hom_eq
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              (f : I_{V} --> P y₁ x₁)
              (g : I_{V} --> P y₂ x₂)
    : graph_enriched_profunctor_enrichment_hom_pr1 f g
      · mon_rinvunitor _
      · (identity _ #⊗ f)
      · rmap_e P y₁ x₁ x₂
      =
      graph_enriched_profunctor_enrichment_hom_pr2 f g
      · mon_rinvunitor _
      · (identity _ #⊗ g)
      · lmap_e P y₂ y₁ x₂.
  Proof.
    unfold graph_enriched_profunctor_enrichment_hom_pr1.
    unfold graph_enriched_profunctor_enrichment_hom_pr2.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    apply EqualizerEqAr.
  Qed.

  Definition graph_enriched_profunctor_enrichment_hom_mor
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : I_{V} --> P y₁ x₁}
             {g : I_{V} --> P y₂ x₂}
             (v : V)
             (l : v --> E₁ ⦃ x₁ , x₂ ⦄)
             (r : v --> E₂ ⦃ y₁ , y₂ ⦄)
             (p : l · mon_rinvunitor _ · identity _ #⊗ f · rmap_e P y₁ x₁ x₂
                  =
                  r · mon_rinvunitor _ · identity _ #⊗ g · lmap_e P y₂ y₁ x₂)
    : v --> graph_enriched_profunctor_enrichment_hom f g.
  Proof.
    use EqualizerIn.
    - exact (BinProductArrow _ _ l r).
    - abstract
        (unfold graph_enriched_profunctor_enrichment_hom_left ;
         unfold graph_enriched_profunctor_enrichment_hom_right ;
         rewrite !assoc ;
         rewrite BinProductPr1Commutes ;
         rewrite BinProductPr2Commutes ;
         exact p).
  Defined.

  Proposition graph_enriched_profunctor_enrichment_hom_mor_pr1
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : I_{V} --> P y₁ x₁}
              {g : I_{V} --> P y₂ x₂}
              (v : V)
              (l : v --> E₁ ⦃ x₁ , x₂ ⦄)
              (r : v --> E₂ ⦃ y₁ , y₂ ⦄)
              (p : l · mon_rinvunitor _ · identity _ #⊗ f · rmap_e P y₁ x₁ x₂
                   =
                   r · mon_rinvunitor _ · identity _ #⊗ g · lmap_e P y₂ y₁ x₂)
    : graph_enriched_profunctor_enrichment_hom_mor v l r p
      · graph_enriched_profunctor_enrichment_hom_pr1 _ _
      =
      l.
  Proof.
    unfold graph_enriched_profunctor_enrichment_hom_mor.
    unfold graph_enriched_profunctor_enrichment_hom_pr1.
    rewrite !assoc.
    rewrite EqualizerCommutes.
    apply BinProductPr1Commutes.
  Qed.

  Proposition graph_enriched_profunctor_enrichment_hom_mor_pr2
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : I_{V} --> P y₁ x₁}
              {g : I_{V} --> P y₂ x₂}
              (v : V)
              (l : v --> E₁ ⦃ x₁ , x₂ ⦄)
              (r : v --> E₂ ⦃ y₁ , y₂ ⦄)
              (p : l · mon_rinvunitor _ · identity _ #⊗ f · rmap_e P y₁ x₁ x₂
                   =
                   r · mon_rinvunitor _ · identity _ #⊗ g · lmap_e P y₂ y₁ x₂)
    : graph_enriched_profunctor_enrichment_hom_mor v l r p
      · graph_enriched_profunctor_enrichment_hom_pr2 _ _
      =
      r.
  Proof.
    unfold graph_enriched_profunctor_enrichment_hom_mor.
    unfold graph_enriched_profunctor_enrichment_hom_pr2.
    rewrite !assoc.
    rewrite EqualizerCommutes.
    apply BinProductPr2Commutes.
  Qed.

  Proposition graph_enriched_profunctor_enrichment_hom_mor_eq
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : I_{V} --> P y₁ x₁}
              {g : I_{V} --> P y₂ x₂}
              (v : V)
              {h₁ h₂ : v --> graph_enriched_profunctor_enrichment_hom f g}
              (p : h₁ · graph_enriched_profunctor_enrichment_hom_pr1 _ _
                   =
                   h₂ · graph_enriched_profunctor_enrichment_hom_pr1 _ _)
              (q : h₁ · graph_enriched_profunctor_enrichment_hom_pr2 _ _
                   =
                   h₂ · graph_enriched_profunctor_enrichment_hom_pr2 _ _)
    : h₁ = h₂.
  Proof.
    use EqualizerInsEq.
    use BinProductArrowsEq.
    - rewrite !assoc'.
      exact p.
    - rewrite !assoc'.
      exact q.
  Qed.

  (** * 4. Operations for the enrichment *)
  Definition graph_enriched_profunctor_enrichment_id
             {x : C₁}
             {y : C₂}
             (f : I_{V} --> P y x)
    : I_{V} --> graph_enriched_profunctor_enrichment_hom f f.
  Proof.
    use graph_enriched_profunctor_enrichment_hom_mor.
    - apply enriched_id.
    - apply enriched_id.
    - abstract
        (rewrite !tensor_rinvunitor ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite <- !tensor_split' ;
         rewrite !(tensor_split (enriched_id _ _) f) ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite rmap_e_id ;
         rewrite lmap_e_id ;
         apply idpath).
  Defined.

  Proposition graph_enriched_profunctor_enrichment_id_pr1
              {x : C₁}
              {y : C₂}
              (f : I_{V} --> P y x)
    : graph_enriched_profunctor_enrichment_id f
      · graph_enriched_profunctor_enrichment_hom_pr1 _ _
      =
      enriched_id _ _.
  Proof.
    apply graph_enriched_profunctor_enrichment_hom_mor_pr1.
  Qed.

  Proposition graph_enriched_profunctor_enrichment_id_pr2
              {x : C₁}
              {y : C₂}
              (f : I_{V} --> P y x)
    : graph_enriched_profunctor_enrichment_id f
      · graph_enriched_profunctor_enrichment_hom_pr2 _ _
      =
      enriched_id _ _.
  Proof.
    apply graph_enriched_profunctor_enrichment_hom_mor_pr2.
  Qed.

  Section Composition.
    Context {x₁ x₂ x₃ : C₁}
            {y₁ y₂ y₃ : C₂}
            (f : I_{V} --> P y₁ x₁)
            (g : I_{V} --> P y₂ x₂)
            (h : I_{V} --> P y₃ x₃).

    Let l : graph_enriched_profunctor_enrichment_hom g h
            ⊗
            graph_enriched_profunctor_enrichment_hom f g
            -->
            E₁ ⦃ x₁ , x₃ ⦄
      := graph_enriched_profunctor_enrichment_hom_pr1 _ _
         #⊗
         graph_enriched_profunctor_enrichment_hom_pr1 _ _
         · enriched_comp _ _ _ _.

    Let r : graph_enriched_profunctor_enrichment_hom g h
            ⊗
            graph_enriched_profunctor_enrichment_hom f g
            -->
            E₂ ⦃ y₁ , y₃ ⦄
      := graph_enriched_profunctor_enrichment_hom_pr2 _ _
         #⊗
         graph_enriched_profunctor_enrichment_hom_pr2 _ _
         · enriched_comp _ _ _ _.

    Proposition graph_enriched_profunctor_enrichment_comp_eq
      : l · mon_rinvunitor _ · identity _ #⊗ f · rmap_e P y₁ x₁ x₃
        =
        r · mon_rinvunitor _ · identity _ #⊗ h · lmap_e P y₃ y₁ x₃.
    Proof.
      unfold l, r.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite rmap_e_comp.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- mon_rinvunitor_triangle.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- !tensor_comp_l_id_r.
        apply maponpaths_2.
        apply maponpaths.
        apply graph_enriched_profunctor_enrichment_hom_eq.
      }
      etrans.
      {
        rewrite tensor_comp_l_id_r.
        rewrite !assoc'.
        apply maponpaths.
        apply lmap_e_rmap_e'.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite lmap_e_comp'.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite <- tensor_comp_r_id_r.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_split'.
        rewrite !assoc.
        rewrite <- tensor_rinvunitor.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_lassociator.
          apply idpath.
        }
        rewrite !assoc.
        rewrite <- mon_rinvunitor_triangle.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_mor.
        rewrite !id_right.
        apply maponpaths_2.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite id_right.
        refine (!_).
        apply graph_enriched_profunctor_enrichment_hom_eq.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_l_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        do 2 rewrite tensor_comp_l_id_r.
        rewrite !assoc.
        rewrite <- tensor_sym_mon_braiding.
        do 3 apply maponpaths_2.
        apply tensor_split'.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths_2.
        apply tensor_split'.
      }
      rewrite !assoc'.
      apply maponpaths.
      do 2 rewrite tensor_comp_l_id_l.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite sym_mon_tensor_lassociator'.
        rewrite !assoc'.
        rewrite mon_rassociator_lassociator.
        rewrite id_right.
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- mon_inv_triangle.
      rewrite <- tensor_comp_id_l.
      rewrite sym_mon_braiding_linvunitor.
      apply idpath.
    Qed.

    Definition graph_enriched_profunctor_enrichment_comp
      : graph_enriched_profunctor_enrichment_hom g h
        ⊗
        graph_enriched_profunctor_enrichment_hom f g
        -->
        graph_enriched_profunctor_enrichment_hom f h.
    Proof.
      use graph_enriched_profunctor_enrichment_hom_mor.
      - exact l.
      - exact r.
      - exact graph_enriched_profunctor_enrichment_comp_eq.
    Defined.

    Proposition graph_enriched_profunctor_enrichment_comp_pr1
      : graph_enriched_profunctor_enrichment_comp
        · graph_enriched_profunctor_enrichment_hom_pr1 _ _
        =
        l.
    Proof.
      apply graph_enriched_profunctor_enrichment_hom_mor_pr1.
    Qed.

    Proposition graph_enriched_profunctor_enrichment_comp_pr2
      : graph_enriched_profunctor_enrichment_comp
        · graph_enriched_profunctor_enrichment_hom_pr2 _ _
        =
        r.
    Proof.
      apply graph_enriched_profunctor_enrichment_hom_mor_pr2.
    Qed.
  End Composition.

  Definition graph_enriched_profunctor_enrichment_from_arr
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : I_{V} --> P y₁ x₁}
             {g : I_{V} --> P y₂ x₂}
             {hx : x₁ --> x₂}
             {hy : y₁ --> y₂}
             (p : g · lmap_e_arr P _ hy = f · rmap_e_arr P hx _)
    : I_{V} --> graph_enriched_profunctor_enrichment_hom f g.
  Proof.
    use graph_enriched_profunctor_enrichment_hom_mor.
    - exact (enriched_from_arr E₁ hx).
    - exact (enriched_from_arr E₂ hy).
    - abstract
        (rewrite !tensor_rinvunitor ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite <- !tensor_split' ;
         rewrite (tensor_split (enriched_from_arr _ _) f) ;
         rewrite (tensor_split (enriched_from_arr _ _) g) ;
         unfold lmap_e_arr, rmap_e_arr in p ;
         rewrite !assoc in p ;
         rewrite !tensor_linvunitor in p ;
         pose proof (maponpaths (λ z, mon_lunitor _ · z) p) as q ;
         cbn in q ;
         rewrite !assoc in q ;
         rewrite !mon_lunitor_linvunitor in q ;
         rewrite !id_left in q ;
         exact (!q)).
  Defined.

  Proposition graph_enriched_profunctor_enrichment_from_arr_pr1
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : I_{V} --> P y₁ x₁}
              {g : I_{V} --> P y₂ x₂}
              {hx : x₁ --> x₂}
              {hy : y₁ --> y₂}
              (p : g · lmap_e_arr P _ hy = f · rmap_e_arr P hx _)
    : graph_enriched_profunctor_enrichment_from_arr p
      · graph_enriched_profunctor_enrichment_hom_pr1 _ _
      =
      enriched_from_arr E₁ hx.
  Proof.
    apply graph_enriched_profunctor_enrichment_hom_mor_pr1.
  Qed.

  Proposition graph_enriched_profunctor_enrichment_from_arr_pr2
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : I_{V} --> P y₁ x₁}
              {g : I_{V} --> P y₂ x₂}
              {hx : x₁ --> x₂}
              {hy : y₁ --> y₂}
              (p : g · lmap_e_arr P _ hy = f · rmap_e_arr P hx _)
    : graph_enriched_profunctor_enrichment_from_arr p
      · graph_enriched_profunctor_enrichment_hom_pr2 _ _
      =
      enriched_from_arr E₂ hy.
  Proof.
    apply graph_enriched_profunctor_enrichment_hom_mor_pr2.
  Qed.

  Section ToArr.
    Context {xyf₁ xyf₂ : graph_enriched_profunctor_ob}
            (h : I_{V}
                 -->
                 graph_enriched_profunctor_enrichment_hom
                   (graph_enriched_profunctor_ob_mor xyf₁)
                   (graph_enriched_profunctor_ob_mor xyf₂)).

    Let k₁ : graph_enriched_profunctor_ob_pr1 xyf₁
             -->
             graph_enriched_profunctor_ob_pr1 xyf₂
      := enriched_to_arr _ (h · graph_enriched_profunctor_enrichment_hom_pr2 _ _).

    Let k₂ : graph_enriched_profunctor_ob_pr2 xyf₁
             -->
             graph_enriched_profunctor_ob_pr2 xyf₂
      := enriched_to_arr _ (h · graph_enriched_profunctor_enrichment_hom_pr1 _ _).

    Proposition graph_enriched_profunctor_enrichment_to_arr_eq
      : graph_enriched_profunctor_ob_mor xyf₂
        · lmap_e_arr P (graph_enriched_profunctor_ob_pr2 xyf₂) k₁
        =
        graph_enriched_profunctor_ob_mor xyf₁
        · rmap_e_arr P k₂ (graph_enriched_profunctor_ob_pr1 xyf₁).
    Proof.
      unfold k₁, k₂.
      cbn.
      unfold lmap_e_arr, rmap_e_arr.
      rewrite !enriched_from_to_arr.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_linvunitor.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite !assoc.
        rewrite <- tensor_rinvunitor.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply idpath.
        }
        rewrite !assoc.
        refine (!_).
        apply graph_enriched_profunctor_enrichment_hom_eq.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_linvunitor.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite !assoc.
        rewrite <- tensor_rinvunitor.
        apply idpath.
      }
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite !assoc.
      apply idpath.
    Qed.

    Definition graph_enriched_profunctor_enrichment_to_arr
      : xyf₁ --> xyf₂.
    Proof.
      use make_graph_enriched_profunctor_mor.
      - exact k₁.
      - exact k₂.
      - exact graph_enriched_profunctor_enrichment_to_arr_eq.
    Defined.
  End ToArr.

  Definition graph_enriched_profunctor_enrichment_data
    : enrichment_data graph_enriched_profunctor V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - intros xyf₁ xyf₂.
      exact (graph_enriched_profunctor_enrichment_hom (pr22 xyf₁) (pr22 xyf₂)).
    - intros xyf.
      exact (graph_enriched_profunctor_enrichment_id (pr22 xyf)).
    - intros xyf₁ xyf₂ xyf₃.
      exact (graph_enriched_profunctor_enrichment_comp (pr22 xyf₁) (pr22 xyf₂) (pr22 xyf₃)).
    - intros xyf₁ xyf₂ h.
      exact (graph_enriched_profunctor_enrichment_from_arr (pr22 h)).
    - intros xyf₁ xyf₂ h.
      exact (graph_enriched_profunctor_enrichment_to_arr h).
  Defined.

  (** * 5. Laws for the enrichment *)
  Proposition graph_enriched_profunctor_enrichment_laws
    : enrichment_laws graph_enriched_profunctor_enrichment_data.
  Proof.
    repeat split.
    - intros xyf₁ xyf₂ ; cbn.
      use graph_enriched_profunctor_enrichment_hom_mor_eq.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite graph_enriched_profunctor_enrichment_id_pr1.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        rewrite tensor_lunitor.
        apply idpath.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite graph_enriched_profunctor_enrichment_id_pr2.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        rewrite tensor_lunitor.
        apply idpath.
    - intros xyf₁ xyf₂ ; cbn.
      use graph_enriched_profunctor_enrichment_hom_mor_eq.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite graph_enriched_profunctor_enrichment_id_pr1.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        apply idpath.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite graph_enriched_profunctor_enrichment_id_pr2.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        apply idpath.
    - intros xyf₁ xyf₂ xyf₃ xyf₄ ; cbn.
      use graph_enriched_profunctor_enrichment_hom_mor_eq.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        etrans.
        {
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_left.
          rewrite graph_enriched_profunctor_enrichment_comp_pr1.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite enrichment_assoc.
          rewrite !assoc.
          rewrite tensor_lassociator.
          apply idpath.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite id_left, id_right.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        etrans.
        {
          rewrite !assoc.
          rewrite <- tensor_comp_mor.
          rewrite id_left.
          rewrite graph_enriched_profunctor_enrichment_comp_pr2.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite enrichment_assoc.
          rewrite !assoc.
          rewrite tensor_lassociator.
          apply idpath.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite id_left, id_right.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        apply idpath.
    - intros xyf₁ xyf₂ f.
      use eq_graph_enriched_profunctor_mor.
      + cbn.
        rewrite graph_enriched_profunctor_enrichment_from_arr_pr2.
        rewrite enriched_to_from_arr.
        apply idpath.
      + cbn.
        rewrite graph_enriched_profunctor_enrichment_from_arr_pr1.
        rewrite enriched_to_from_arr.
        apply idpath.
    - intros xyf₁ xyf₂ f ; cbn.
      use graph_enriched_profunctor_enrichment_hom_mor_eq.
      + rewrite graph_enriched_profunctor_enrichment_from_arr_pr1.
        rewrite enriched_from_to_arr.
        apply idpath.
      + rewrite graph_enriched_profunctor_enrichment_from_arr_pr2.
        rewrite enriched_from_to_arr.
        apply idpath.
    - intros xyf.
      use eq_graph_enriched_profunctor_mor.
      + cbn.
        rewrite graph_enriched_profunctor_enrichment_id_pr2.
        rewrite enriched_to_arr_id.
        apply idpath.
      + cbn.
        rewrite graph_enriched_profunctor_enrichment_id_pr1.
        rewrite enriched_to_arr_id.
        apply idpath.
    - intros xyf₁ xyf₂ xyf₃ h₁ h₂.
      use eq_graph_enriched_profunctor_mor.
      + cbn.
        rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- !tensor_comp_mor.
          rewrite !graph_enriched_profunctor_enrichment_from_arr_pr2.
          apply idpath.
        }
        refine (_ @ !(enriched_to_arr_comp E₂ (pr1 h₁) (pr1 h₂))).
        rewrite !assoc'.
        apply idpath.
      + cbn.
        rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr1.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- !tensor_comp_mor.
          rewrite !graph_enriched_profunctor_enrichment_from_arr_pr1.
          apply idpath.
        }
        refine (_ @ !(enriched_to_arr_comp E₁ (pr12 h₁) (pr12 h₂))).
        rewrite !assoc'.
        apply idpath.
  Qed.

  (** * 6. The enrichment for the graph *)
  Definition graph_enriched_profunctor_enrichment
    : enrichment graph_enriched_profunctor V.
  Proof.
    simple refine (_ ,, _).
    - exact graph_enriched_profunctor_enrichment_data.
    - exact graph_enriched_profunctor_enrichment_laws.
  Defined.

  (** * 7. The first projection *)
  Definition graph_enriched_profunctor_pr1
    : graph_enriched_profunctor ⟶ C₂
    := twosided_disp_category_pr1 _.

  Definition graph_enriched_profunctor_pr1_enrichment
    : functor_enrichment
        graph_enriched_profunctor_pr1
        graph_enriched_profunctor_enrichment
        E₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - intros xyf₁ xyf₂.
      apply graph_enriched_profunctor_enrichment_hom_pr2.
    - abstract
        (intros xyf ; cbn ;
         apply graph_enriched_profunctor_enrichment_id_pr2).
    - abstract
        (intros xyf₁ xyf₂ xyf₃ ; cbn ;
         apply graph_enriched_profunctor_enrichment_comp_pr2).
    - abstract
        (intros xyf₁ xyf₂ h ; cbn ;
         rewrite graph_enriched_profunctor_enrichment_from_arr_pr2 ;
         apply idpath).
  Defined.

  (** * 8. The second projection *)
  Definition graph_enriched_profunctor_pr2
    : graph_enriched_profunctor ⟶ C₁
    := twosided_disp_category_pr2 _.

  Definition graph_enriched_profunctor_pr2_enrichment
    : functor_enrichment
        graph_enriched_profunctor_pr2
        graph_enriched_profunctor_enrichment
        E₁.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - intros xyf₁ xyf₂.
      apply graph_enriched_profunctor_enrichment_hom_pr1.
    - abstract
        (intros xyf ; cbn ;
         apply graph_enriched_profunctor_enrichment_id_pr1).
    - abstract
        (intros xyf₁ xyf₂ xyf₃ ; cbn ;
         apply graph_enriched_profunctor_enrichment_comp_pr1).
    - abstract
        (intros xyf₁ xyf₂ h ; cbn ;
         rewrite graph_enriched_profunctor_enrichment_from_arr_pr1 ;
         apply idpath).
  Defined.

  (** * 9. The square of the graph *)
  Definition enriched_profunctor_graph_square_data
    : enriched_profunctor_transformation_data
        (identity_enriched_profunctor graph_enriched_profunctor_enrichment)
        (precomp_enriched_profunctor
           graph_enriched_profunctor_pr2_enrichment
           graph_enriched_profunctor_pr1_enrichment
           P)
    := λ x y,
       graph_enriched_profunctor_enrichment_hom_pr2 _ _
       · mon_rinvunitor _
       · (identity _ #⊗ graph_enriched_profunctor_ob_mor y)
       · lmap_e P _ _ _.

  Arguments enriched_profunctor_graph_square_data /.

  Proposition enriched_profunctor_graph_square_data_eq
              (x y : graph_enriched_profunctor)
    : enriched_profunctor_graph_square_data x y
      =
      graph_enriched_profunctor_enrichment_hom_pr1 _ _
      · mon_rinvunitor _
      · (identity _ #⊗ graph_enriched_profunctor_ob_mor x)
      · rmap_e P _ _ _.
  Proof.
    refine (!_).
    apply graph_enriched_profunctor_enrichment_hom_eq.
  Qed.

  Proposition enriched_profunctor_graph_square_laws
    : enriched_profunctor_transformation_laws
        enriched_profunctor_graph_square_data.
  Proof.
    split.
    - intros ; cbn.
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!(id_left _) @ _).
        rewrite <- mon_rassociator_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        refine (!_).
        apply lmap_e_comp.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite mon_rinvunitor_triangle.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        rewrite graph_enriched_profunctor_enrichment_comp_pr2.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        do 3 apply maponpaths.
        rewrite tensor_id_id.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        rewrite <- tensor_rinvunitor.
        rewrite !assoc.
        apply idpath.
      }
      apply maponpaths_2.
      rewrite <- tensor_sym_mon_braiding.
      rewrite <- tensor_split'.
      apply idpath.
    - intros.
      rewrite !enriched_profunctor_graph_square_data_eq ; cbn.
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!(id_left _) @ _).
        rewrite <- mon_rassociator_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        refine (!_).
        apply rmap_e_comp.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite mon_rinvunitor_triangle.
        apply idpath.
      }
      refine (!_).
      rewrite graph_enriched_profunctor_enrichment_comp_pr1.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite !assoc'.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_id_id.
      do 3 apply maponpaths_2.
      rewrite <- tensor_split'.
      apply idpath.
  Qed.

  Definition enriched_profunctor_graph_square
    : enriched_profunctor_square
        graph_enriched_profunctor_pr2_enrichment
        graph_enriched_profunctor_pr1_enrichment
        (identity_enriched_profunctor _)
        P.
  Proof.
    use make_enriched_profunctor_transformation.
    - exact enriched_profunctor_graph_square_data.
    - exact enriched_profunctor_graph_square_laws.
  Defined.
End GraphOfEnrichedProfunctor.
