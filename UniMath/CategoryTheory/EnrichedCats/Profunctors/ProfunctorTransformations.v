(******************************************************************************************

 Transformations between enriched profunctors

 In this file, we define transformations between enriched profunctors. For this, we use
 a whiskered style for transformations meaning that we have two naturality laws, namely
 one for the left action and one for the right action. In addition, we simplify the laws,
 since the target is a self-enriched category.

 Content
 1. Transformations between enriched profunctors
 2. Equivalence with the usual definition
 3. Standard transformations of profunctors
 3.1. The identity
 3.2. Composition
 4. Extra laws

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Transformations between enriched profunctors *)
Definition enriched_profunctor_transformation_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : UU
  := ∏ (x : C₂) (y : C₁), P x y --> Q x y.

Definition enriched_profunctor_transformation_laws
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation_data P Q)
  : UU
  := (∏ (x₁ x₂ : C₂)
        (y : C₁),
      identity (E₂ ⦃ x₂, x₁ ⦄) #⊗ τ x₁ y · lmap_e Q x₁ x₂ y
      =
      lmap_e P x₁ x₂ y · τ x₂ y)
     ×
     (∏ (x : C₂)
        (y₁ y₂ : C₁),
      identity (E₁ ⦃ y₁, y₂ ⦄) #⊗ τ x y₁ · rmap_e Q x y₁ y₂
      =
      rmap_e P x y₁ y₂ · τ x y₂).

Proposition isaprop_enriched_profunctor_transformation_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation_data P Q)
  : isaprop (enriched_profunctor_transformation_laws τ).
Proof.
  use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enriched_profunctor_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : UU
  := ∑ (τ : enriched_profunctor_transformation_data P Q),
     enriched_profunctor_transformation_laws τ.

Proposition isaset_enriched_profunctor_transformation
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P Q : E₁ ↛e E₂)
  : isaset (enriched_profunctor_transformation P Q).
Proof.
  use isaset_total2.
  - unfold enriched_profunctor_transformation_data.
    use impred_isaset ; intro x.
    use impred_isaset ; intro y.
    apply homset_property.
  - intro.
    apply isasetaprop.
    apply isaprop_enriched_profunctor_transformation_laws.
Qed.

Definition make_enriched_profunctor_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation_data P Q)
           (Hτ : enriched_profunctor_transformation_laws τ)
  : enriched_profunctor_transformation P Q
  := τ ,, Hτ.

Definition enriched_profunctor_transformation_ob
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
           (x : C₂)
           (y : C₁)
  : P x y --> Q x y
  := pr1 τ x y.

Coercion enriched_profunctor_transformation_ob
  : enriched_profunctor_transformation >-> Funclass.

Proposition enriched_profunctor_transformation_lmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P Q)
            (x₁ x₂ : C₂)
            (y : C₁)
  : identity (E₂ ⦃ x₂, x₁ ⦄) #⊗ τ x₁ y · lmap_e Q x₁ x₂ y
    =
    lmap_e P x₁ x₂ y · τ x₂ y.
Proof.
  exact (pr12 τ x₁ x₂ y).
Defined.

Proposition enriched_profunctor_transformation_rmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P Q)
            (x : C₂)
            (y₁ y₂ : C₁)
  : identity (E₁ ⦃ y₁, y₂ ⦄) #⊗ τ x y₁ · rmap_e Q x y₁ y₂
    =
    rmap_e P x y₁ y₂ · τ x y₂.
Proof.
  exact (pr22 τ x y₁ y₂).
Defined.

Proposition eq_enriched_profunctor_transformation
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            {τ θ : enriched_profunctor_transformation P Q}
            (p : ∏ (x : C₂) (y : C₁), τ x y = θ x y)
  : τ = θ.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_enriched_profunctor_transformation_laws.
  }
  use funextsec ; intro x.
  use funextsec ; intro y.
  exact (p x y).
Qed.

Proposition from_eq_enriched_profunctor_transformation
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            {τ θ : enriched_profunctor_transformation P Q}
            (p : τ = θ)
            (x : C₂)
            (y : C₁)
  : τ x y = θ x y.
Proof.
  exact (maponpaths (λ z, pr1 z x y) p).
Qed.

(** * 2. Equivalence with the usual definition *)
Definition enriched_profunctor_transformation_to_whiskered_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
  : whiskered_enriched_transformation_data
      (enriched_profunctor_to_whiskered P)
      (enriched_profunctor_to_whiskered Q)
  := λ x y, τ x y.

Arguments enriched_profunctor_transformation_to_whiskered_data {V C₁ C₂ E₁ E₂ P Q} τ /.

Proposition enriched_profunctor_transformation_to_whiskered_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P Q)
  : whiskered_enriched_transformation_laws
      (enriched_profunctor_transformation_to_whiskered_data τ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn in *.
    rewrite self_enrichment_precomp, self_enrichment_postcomp.
    use internal_funext.
    intros z h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite internal_beta.
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
      rewrite internal_beta.
      rewrite tensor_comp_id_l.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    clear z h.
    apply enriched_profunctor_transformation_lmap_e.
  - intros x y₁ y₂ ; cbn in *.
    rewrite self_enrichment_precomp, self_enrichment_postcomp.
    use internal_funext.
    intros z h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite !internal_beta.
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite internal_beta.
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
      rewrite internal_beta.
      rewrite tensor_comp_id_l.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    clear z h.
    apply enriched_profunctor_transformation_rmap_e.
Qed.

Definition enriched_profunctor_transformation_to_whiskered
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
  : whiskered_enriched_transformation
      (enriched_profunctor_to_whiskered P)
      (enriched_profunctor_to_whiskered Q).
Proof.
  use make_whiskered_enriched_transformation.
  - exact (enriched_profunctor_transformation_to_whiskered_data τ).
  - exact (enriched_profunctor_transformation_to_whiskered_laws τ).
Defined.

Definition whiskered_to_enriched_profunctor_transformation_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : whiskered_enriched_transformation
                  (enriched_profunctor_to_whiskered P)
                  (enriched_profunctor_to_whiskered Q))
  : enriched_profunctor_transformation_data P Q
  := λ x y, τ x y.

Arguments whiskered_to_enriched_profunctor_transformation_data {V C₁ C₂ E₁ E₂ P Q} τ /.

Proposition whiskered_to_enriched_profunctor_transformation_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P Q : E₁ ↛e E₂}
            (τ : whiskered_enriched_transformation
                   (enriched_profunctor_to_whiskered P)
                   (enriched_profunctor_to_whiskered Q))
  : enriched_profunctor_transformation_laws
      (whiskered_to_enriched_profunctor_transformation_data τ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    pose (maponpaths
            (λ z, z #⊗ identity _ · internal_eval _ _)
            (whiskered_enriched_transformation_natural_left τ x₁ x₂ y)) as p.
    cbn in p.
    rewrite self_enrichment_precomp, self_enrichment_postcomp in p.
    rewrite !tensor_comp_id_r in p.
    rewrite !assoc' in p.
    rewrite !internal_beta in p.
    rewrite !assoc in p.
    rewrite !internal_beta in p.
    rewrite p ; clear p.
    refine (!_).
    etrans.
    {
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    pose (maponpaths
            (λ z, z #⊗ identity _ · internal_eval _ _)
            (whiskered_enriched_transformation_natural_right τ x y₁ y₂)) as p.
    cbn in p.
    rewrite self_enrichment_precomp, self_enrichment_postcomp in p.
    rewrite !tensor_comp_id_r in p.
    rewrite !assoc' in p.
    rewrite !internal_beta in p.
    rewrite !assoc in p.
    rewrite !internal_beta in p.
    rewrite p ; clear p.
    refine (!_).
    etrans.
    {
      rewrite <- tensor_split'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    apply idpath.
Qed.

Definition whiskered_to_enriched_profunctor_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : whiskered_enriched_transformation
                  (enriched_profunctor_to_whiskered P)
                  (enriched_profunctor_to_whiskered Q))
  : enriched_profunctor_transformation P Q.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (whiskered_to_enriched_profunctor_transformation_data τ).
  - exact (whiskered_to_enriched_profunctor_transformation_laws τ).
Defined.

Definition whiskered_enriched_profunctor_transformation_weq
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : whiskered_enriched_transformation
      (enriched_profunctor_to_whiskered P)
      (enriched_profunctor_to_whiskered Q)
    ≃
    enriched_profunctor_transformation P Q.
Proof.
  use weq_iso.
  - exact whiskered_to_enriched_profunctor_transformation.
  - exact enriched_profunctor_transformation_to_whiskered.
  - abstract
      (intro τ ;
       use eq_whiskered_enriched_transformation ;
       intros ;
       apply idpath).
  - abstract
      (intro τ ;
       use eq_enriched_profunctor_transformation ;
       intros ;
       apply idpath).
Defined.

Definition enriched_profunctor_transformation_nat_trans_weq
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P Q : E₁ ↛e E₂)
  : enriched_nat_trans
      (enriched_curried_bifunctor_to_bifunctor
         (enriched_whiskered_bifunctor_to_curried
            (enriched_profunctor_to_whiskered P)))
      (enriched_curried_bifunctor_to_bifunctor
         (enriched_whiskered_bifunctor_to_curried
            (enriched_profunctor_to_whiskered Q)))
    ≃
    enriched_profunctor_transformation P Q
  := (whiskered_enriched_profunctor_transformation_weq P Q
      ∘ enriched_nat_trans_whiskered_weq _ _)%weq.

(** * 3. Standard transformations of profunctors *)

(** ** 3.1. The identity *)
Definition enriched_profunctor_id_transformation_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
  : enriched_profunctor_transformation_data P P
  := λ _ _, identity _.

Arguments enriched_profunctor_id_transformation_data {V C₁ C₂ E₁ E₂} P /.

Proposition enriched_profunctor_id_transformation_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
  : enriched_profunctor_transformation_laws
      (enriched_profunctor_id_transformation_data P).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_id_id.
    rewrite id_left, id_right.
    apply idpath.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_id_id.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Definition enriched_profunctor_id_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
  : enriched_profunctor_transformation P P.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (enriched_profunctor_id_transformation_data P).
  - exact (enriched_profunctor_id_transformation_laws P).
Defined.

(** ** 3.2. Composition *)
Definition enriched_profunctor_comp_transformation_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P₁ P₂ P₃ : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P₁ P₂)
           (θ : enriched_profunctor_transformation P₂ P₃)
  : enriched_profunctor_transformation_data P₁ P₃
  := λ x y, τ x y · θ x y.

Arguments enriched_profunctor_comp_transformation_data {V C₁ C₂ E₁ E₂ P₁ P₂ P₃} τ θ /.

Proposition enriched_profunctor_comp_transformation_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {P₁ P₂ P₃ : E₁ ↛e E₂}
            (τ : enriched_profunctor_transformation P₁ P₂)
            (θ : enriched_profunctor_transformation P₂ P₃)
  : enriched_profunctor_transformation_laws
      (enriched_profunctor_comp_transformation_data τ θ).
Proof.
  split.
  - intros x₁ x₂ y ; cbn.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_lmap_e.
    rewrite !assoc.
    rewrite enriched_profunctor_transformation_lmap_e.
    rewrite !assoc'.
    apply idpath.
  - intros x y₁ y₂ ; cbn.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_rmap_e.
    rewrite !assoc.
    rewrite enriched_profunctor_transformation_rmap_e.
    rewrite !assoc'.
    apply idpath.
Qed.

Definition enriched_profunctor_comp_transformation
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P₁ P₂ P₃ : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P₁ P₂)
           (θ : enriched_profunctor_transformation P₂ P₃)
  : enriched_profunctor_transformation P₁ P₃.
Proof.
  use make_enriched_profunctor_transformation.
  - exact (enriched_profunctor_comp_transformation_data τ θ).
  - exact (enriched_profunctor_comp_transformation_laws τ θ).
Defined.

(** * 4. Extra laws *)
Definition enriched_profunctor_transformation_lmap_e_arr
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
           {y₁ y₂ : C₂}
           (g : y₁ --> y₂)
           (x : C₁)
  : τ y₂ x · lmap_e_arr Q x g
    =
    lmap_e_arr P x g · τ y₁ x.
Proof.
  unfold lmap_e_arr.
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_lmap_e.
    apply idpath.
  }
  rewrite !assoc.
  apply idpath.
Qed.

Definition enriched_profunctor_transformation_rmap_e_arr
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {P Q : E₁ ↛e E₂}
           (τ : enriched_profunctor_transformation P Q)
           (y : C₂)
           {x₁ x₂ : C₁}
           (f : x₁ --> x₂)
  : τ y x₁ · rmap_e_arr Q f y
    =
    rmap_e_arr P f y · τ y x₂.
Proof.
  unfold rmap_e_arr.
  etrans.
  {
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    rewrite !assoc'.
    rewrite enriched_profunctor_transformation_rmap_e.
    apply idpath.
  }
  rewrite !assoc.
  apply idpath.
Qed.
