(******************************************************************************************

 Enriched profunctors

 In this file, we define enriched profunctors. Usually, enriched profunctors are defined as
 follows: let `V` be a symmetric monoidal closed category, then an enriched profunctor from
 a `V`-enriched category `E₁` to a `V`-enriched category `E₂` is given by an enriched
 profunctor from the tensor of `E₂^op` and `E₁` to the self-enriched category `V`.

 We made a couple of variations to this definition.
 1. First of all, we use a whiskered style. Concretely, this that rather than having a
    single functorial action which takes morphisms in `E₂` and in `E₁`, we have two
    functorial actions. One that takes a morphism in `E₂` and one that takes a morphism in
    `E₁`. This concept is further explained in the file `WhiskeredBifunctors` in the directory
    `EnrichedCats.Bifunctors`.
 2. Second, since we are looking at `E₂^op`, we modify our definition accordingly. More
    specifically, in [enriched_profunctor_data]. we do not mention the opposite category
    explicitly. Instead, we have an action `E₂ ⦃ x₂, x₁ ⦄ ⊗ P x₁ y --> P x₂ y` where we
    already reversed the direction.
 3. Third, the target of an enriched profunctor is the self-enriched category. In the
    self-enriched category, the hom-objects are given by the right adjoint of the tensor
    (i.e., linear function spaces). As such, whenever we are going to construct a morphism
    to such a hom-object, we are going to use a exponential transposes (i.e., lambda
    abstractions). For this reason, in the definition [enriched_profunctor_data], we do
    not mention the right adjoint, but we already took all necessary exponential transposes.
 4. Finally, the laws are rephrased to fit nicely with the aforementioned changes. The
    main difference is caused by the fact that the left and right action are both defined
    as a exponential transpose (i.e., lambda abstraction), and this allows us to simplify
    the laws of whiskered bifunctors (see [enriched_profunctor_laws]).

 We also show that our definition is equivalent to the definition of enriched profunctors
 via whiskered bifunctors, and thus it is equivalent to the usual definition of enriched
 profunctors. Finally, we give an action on morphisms of profunctors

 Contents
 1. Enriched profunctors
 2. Accessors
 3. Equivalence with whiskered bifunctors
 4. Action on morphisms in the underlying category

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
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Enriched profunctors *)
Definition enriched_profunctor_data
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (P : C₂ → C₁ → V),
     (∏ (x₁ x₂ : C₂)
        (y : C₁),
      E₂ ⦃ x₂, x₁ ⦄ ⊗ P x₁ y --> P x₂ y)
     ×
     (∏ (x : C₂)
        (y₁ y₂ : C₁),
      E₁ ⦃ y₁, y₂ ⦄ ⊗ P x y₁ --> P x y₂).

Definition make_enriched_profunctor_data
           {V : sym_mon_closed_cat}
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
  : enriched_profunctor_data E₁ E₂
  := P ,, Pl ,, Pr.

Definition enriched_profunctor_ob
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : enriched_profunctor_data E₁ E₂)
           (y : C₂)
           (x : C₁)
  : V
  := pr1 P y x.

Coercion enriched_profunctor_ob : enriched_profunctor_data >-> Funclass.

Definition lmap_e
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : enriched_profunctor_data E₁ E₂)
           (x₁ x₂ : C₂)
           (y : C₁)
  : E₂ ⦃ x₂, x₁ ⦄ ⊗ P x₁ y --> P x₂ y
  := pr12 P x₁ x₂ y.

Definition rmap_e
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : enriched_profunctor_data E₁ E₂)
           (x : C₂)
           (y₁ y₂ : C₁)
  : E₁ ⦃ y₁, y₂ ⦄ ⊗ P x y₁ --> P x y₂
  := pr22 P x y₁ y₂.

Definition enriched_profunctor_laws
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : enriched_profunctor_data E₁ E₂)
  : UU
  := (∏ (x : C₂)
        (y : C₁),
      enriched_id E₂ x #⊗ identity (P x y) · lmap_e P x x y
      =
      mon_lunitor (P x y))
     ×
     (∏ (x : C₂)
        (y : C₁),
      enriched_id E₁ y #⊗ identity (P x y) · rmap_e P x y y
      =
      mon_lunitor (P x y))
     ×
     (∏ (x₁ x₂ x₃ : C₂)
        (y : C₁),
      (sym_mon_braiding V _ _ · enriched_comp E₂ x₃ x₂ x₁) #⊗ identity _
      · lmap_e P x₁ x₃ y
      =
      mon_lassociator _ _ _
      · identity _ #⊗ lmap_e P x₁ x₂ y
      · lmap_e P x₂ x₃ y)
     ×
     (∏ (x : C₂)
        (y₁ y₂ y₃ : C₁),
      enriched_comp E₁ y₁ y₂ y₃ #⊗ identity (P x y₁)
      · rmap_e P x y₁ y₃
      =
      mon_lassociator _ _ _
      · identity _ #⊗ rmap_e P x y₁ y₂
      · rmap_e P x y₂ y₃)
     ×
     (∏ (x₁ x₂ : C₂)
        (y₁ y₂ : C₁),
     sym_mon_braiding V _ _ #⊗ identity _
     · mon_lassociator _ _ _
     · identity _ #⊗ lmap_e P x₁ x₂ y₁
     · rmap_e P x₂ y₁ y₂
     =
     mon_lassociator _ _ _
     · identity _ #⊗ rmap_e P x₁ y₁ y₂
     · lmap_e P x₁ x₂ y₂).

Proposition isaprop_enriched_profunctor_laws
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : enriched_profunctor_data E₁ E₂)
  : isaprop (enriched_profunctor_laws P).
Proof.
  repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enriched_profunctor
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : UU
  := ∑ (P : enriched_profunctor_data E₁ E₂),
     enriched_profunctor_laws P.

Notation "E₁ ↛e E₂" := (enriched_profunctor E₁ E₂)
                         (at level 99, only parsing) : cat. (* \nrightarrow *)

Definition make_enriched_profunctor
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : enriched_profunctor_data E₁ E₂)
           (HP : enriched_profunctor_laws P)
  : E₁ ↛e E₂
  := P ,, HP.

Coercion enriched_profunctor_to_data
         {V : sym_mon_closed_cat}
         {C₁ C₂ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         (P : E₁ ↛e E₂)
  : enriched_profunctor_data E₁ E₂.
Proof.
  exact (pr1 P).
Defined.

(** * 2. Accessors *)
Section Accessors.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : E₁ ↛e E₂).

  Proposition lmap_e_id
              (x : C₂)
              (y : C₁)
    : enriched_id E₂ x #⊗ identity (P x y) · lmap_e P x x y
      =
      mon_lunitor (P x y).
  Proof.
    exact (pr12 P x y).
  Defined.

  Proposition rmap_e_id
              (x : C₂)
              (y : C₁)
    : enriched_id E₁ y #⊗ identity (P x y) · rmap_e P x y y
      =
      mon_lunitor (P x y).
  Proof.
    exact (pr122 P x y).
  Defined.

  Proposition lmap_e_comp
              (x₁ x₂ x₃ : C₂)
              (y : C₁)
    : (sym_mon_braiding V _ _ · enriched_comp E₂ x₃ x₂ x₁) #⊗ identity _
      · lmap_e P x₁ x₃ y
      =
      mon_lassociator _ _ _
      · identity _ #⊗ lmap_e P x₁ x₂ y
      · lmap_e P x₂ x₃ y.
  Proof.
    exact (pr1 (pr222 P) x₁ x₂ x₃ y).
  Defined.

  Proposition lmap_e_comp'
              (x₁ x₂ x₃ : C₂)
              (y : C₁)
    : enriched_comp E₂ x₃ x₂ x₁ #⊗ identity _
      · lmap_e P x₁ x₃ y
      =
      (sym_mon_braiding V _ _ #⊗ identity _)
      · mon_lassociator _ _ _
      · identity _ #⊗ lmap_e P x₁ x₂ y
      · lmap_e P x₂ x₃ y.
  Proof.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- lmap_e_comp.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition lmap_e_lmap_e
              (x₁ x₂ x₃ : C₂)
              (y : C₁)
    : identity _ #⊗ lmap_e P x₁ x₂ y
      · lmap_e P x₂ x₃ y
      =
      mon_rassociator _ _ _
      · (sym_mon_braiding V _ _ #⊗ identity _)
      · enriched_comp E₂ x₃ x₂ x₁ #⊗ identity _
      · lmap_e P x₁ x₃ y.
  Proof.
    rewrite !assoc'.
    rewrite lmap_e_comp'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition rmap_e_comp
              (x : C₂)
              (y₁ y₂ y₃ : C₁)
    : enriched_comp E₁ y₁ y₂ y₃ #⊗ identity (P x y₁)
      · rmap_e P x y₁ y₃
      =
      mon_lassociator _ _ _
      · identity _ #⊗ rmap_e P x y₁ y₂
      · rmap_e P x y₂ y₃.
  Proof.
    exact (pr12 (pr222 P) x y₁ y₂ y₃).
  Defined.

  Proposition rmap_e_rmap_e
              (x : C₂)
              (y₁ y₂ y₃ : C₁)
    : identity _ #⊗ rmap_e P x y₁ y₂
      · rmap_e P x y₂ y₃
      =
      mon_rassociator _ _ _
      · enriched_comp E₁ y₁ y₂ y₃ #⊗ identity (P x y₁)
      · rmap_e P x y₁ y₃.
  Proof.
    rewrite !assoc'.
    rewrite rmap_e_comp.
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition lmap_e_rmap_e
              (x₁ x₂ : C₂)
              (y₁ y₂ : C₁)
    : sym_mon_braiding V _ _ #⊗ identity _
     · mon_lassociator _ _ _
     · identity _ #⊗ lmap_e P x₁ x₂ y₁
     · rmap_e P x₂ y₁ y₂
     =
     mon_lassociator _ _ _
     · identity _ #⊗ rmap_e P x₁ y₁ y₂
     · lmap_e P x₁ x₂ y₂.
  Proof.
    exact (pr22 (pr222 P) x₁ x₂ y₁ y₂).
  Defined.

  Proposition lmap_e_rmap_e'
              (x₁ x₂ : C₂)
              (y₁ y₂ : C₁)
    : identity _ #⊗ lmap_e P x₁ x₂ y₁
     · rmap_e P x₂ y₁ y₂
     =
     mon_rassociator _ _ _
     · sym_mon_braiding V _ _ #⊗ identity _
     · mon_lassociator _ _ _
     · identity _ #⊗ rmap_e P x₁ y₁ y₂
     · lmap_e P x₁ x₂ y₂.
  Proof.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite <- lmap_e_rmap_e.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_r_id_r.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition rmap_e_lmap_e
              (x₁ x₂ : C₂)
              (y₁ y₂ : C₁)
    : identity _ #⊗ rmap_e P x₁ y₁ y₂
      · lmap_e P x₁ x₂ y₂
      =
      mon_rassociator _ _ _
     · sym_mon_braiding V _ _ #⊗ identity _
     · mon_lassociator _ _ _
     · identity _ #⊗ lmap_e P x₁ x₂ y₁
     · rmap_e P x₂ y₁ y₂.
  Proof.
    rewrite !assoc'.
    rewrite lmap_e_rmap_e'.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_r_id_r.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.
End Accessors.

(** * 3. Equivalence with whiskered bifunctors *)
Section FromEnrichedProfunctor.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : E₁ ↛e E₂).

  Definition enriched_profunctor_to_whiskered_data
    : enriched_whiskered_bifunctor_data
        (op_enrichment V E₂) E₁
        (self_enrichment V).
  Proof.
    use make_enriched_whiskered_bifunctor_data.
    - exact (λ y x, P y x).
    - exact (λ x₁ x₂ y, internal_lam (lmap_e P x₁ x₂ y)).
    - exact (λ x y₁ y₂, internal_lam (rmap_e P x y₁ y₂)).
  Defined.

  Proposition enriched_profunctor_to_whiskered_laws
    : enriched_whiskered_bifunctor_laws
        enriched_profunctor_to_whiskered_data.
  Proof.
    repeat split ; cbn.
    - intros x y.
      unfold internal_id.
      use internal_funext.
      intros z h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear z h.
      exact (lmap_e_id P x y).
    - intros x y.
      unfold internal_id.
      use internal_funext.
      intros z h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear z h.
      exact (rmap_e_id P x y).
    - intros x₁ x₂ x₃ y.
      use internal_funext.
      intros z h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      rewrite <- tensor_lassociator.
      rewrite tensor_id_id.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear z h.
      rewrite !assoc.
      exact (lmap_e_comp P x₁ x₂ x₃ y).
    - intros x y₁ y₂ y₃.
      use internal_funext.
      intros z h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      rewrite <- tensor_lassociator.
      rewrite tensor_id_id.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      clear z h.
      rewrite !assoc.
      exact (rmap_e_comp P x y₁ y₂ y₃).
    - intros x₁ x₂ y₁ y₂.
      use internal_funext.
      intros z h.
      unfold internal_comp.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_lassociator.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite tensor_comp_id_l.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite !tensor_id_id.
      apply maponpaths.
      clear z h.
      rewrite id_left.
      rewrite !assoc.
      exact (lmap_e_rmap_e P x₁ x₂ y₁ y₂).
  Qed.

  Definition enriched_profunctor_to_whiskered
    : enriched_whiskered_bifunctor
        (op_enrichment V E₂) E₁
        (self_enrichment V).
  Proof.
    use make_enriched_whiskered_bifunctor.
    - exact enriched_profunctor_to_whiskered_data.
    - exact enriched_profunctor_to_whiskered_laws.
  Defined.
End FromEnrichedProfunctor.

Section ToEnrichedProfunctor.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          (P : enriched_whiskered_bifunctor
                 (op_enrichment V E₂) E₁
                 (self_enrichment V)).

  Definition enriched_whiskered_bifunctor_to_profunctor_data
    : enriched_profunctor_data E₁ E₂.
  Proof.
    use make_enriched_profunctor_data.
    - exact (λ x y, P x y).
    - exact (λ x₁ x₂ y,
             enriched_whiskered_bifunctor_left P x₁ x₂ y #⊗ identity _
             · internal_eval _ _).
    - exact (λ x y₁ y₂,
             enriched_whiskered_bifunctor_right P x y₁ y₂ #⊗ identity _
             · internal_eval _ _).
  Defined.

  Proposition enriched_whiskered_bifunctor_to_profunctor_laws
    : enriched_profunctor_laws
        enriched_whiskered_bifunctor_to_profunctor_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (enriched_whiskered_bifunctor_left_id P x y).
      }
      cbn.
      unfold internal_id.
      rewrite internal_beta.
      apply idpath.
    - intros x y ; cbn.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (enriched_whiskered_bifunctor_right_id P x y).
      }
      cbn.
      unfold internal_id.
      rewrite internal_beta.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (enriched_whiskered_bifunctor_left_comp P x₁ x₂ x₃ y).
      }
      cbn.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lassociator.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left, !id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (enriched_whiskered_bifunctor_right_comp P x₁ x₂ x₃ y).
      }
      cbn.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite tensor_lassociator.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left, !id_right.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.
      pose (maponpaths
              (λ z, z #⊗ identity _ · internal_eval _ _)
              (enriched_whiskered_bifunctor_left_right P x₁ x₂ y₁ y₂)) as p.
      cbn in p.
      rewrite !tensor_comp_r_id_r in p.
      rewrite !assoc' in p.
      unfold internal_comp in p.
      rewrite !internal_beta in p.
      rewrite !assoc in p.
      rewrite tensor_lassociator in p.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        refine (_ @ p).
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        apply idpath.
      }
      clear p.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_comp_mor.
      rewrite !id_right, id_left.
      apply idpath.
  Qed.

  Definition enriched_whiskered_bifunctor_to_profunctor
    : E₁ ↛e E₂.
  Proof.
    use make_enriched_profunctor.
    - exact enriched_whiskered_bifunctor_to_profunctor_data.
    - exact enriched_whiskered_bifunctor_to_profunctor_laws.
  Defined.
End ToEnrichedProfunctor.

Section Inverses.
  Context {V : sym_mon_closed_cat}
          {C₁ C₂ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}.

  Proposition enriched_profunctor_whiskered_bifunctor_weq_left
              (P : enriched_whiskered_bifunctor
                     (op_enrichment V E₂) E₁
                     (self_enrichment V))
    : enriched_profunctor_to_whiskered
        (enriched_whiskered_bifunctor_to_profunctor P)
      =
      P.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enriched_whiskered_bifunctor_laws.
    }
    refine (maponpaths (λ z, pr11 P ,, z) _).
    use pathsdirprod.
    - use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y ; cbn.
      use internal_funext.
      intros z h.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    - use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y ; cbn.
      use internal_funext.
      intros z h.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
  Qed.

  Proposition enriched_profunctor_whiskered_bifunctor_weq_right
              (P : E₁ ↛e E₂)
    : enriched_whiskered_bifunctor_to_profunctor
        (enriched_profunctor_to_whiskered P)
      =
      P.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enriched_profunctor_laws.
    }
    refine (maponpaths (λ z, pr11 P ,, z) _).
    use pathsdirprod.
    - use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y ; cbn.
      apply internal_beta.
    - use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y ; cbn.
      apply internal_beta.
  Qed.
End Inverses.

Definition enriched_profunctor_whiskered_bifunctor_weq
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : enriched_whiskered_bifunctor
      (op_enrichment V E₂) E₁
      (self_enrichment V)
    ≃
    (E₁ ↛e E₂).
Proof.
  use weq_iso.
  - exact enriched_whiskered_bifunctor_to_profunctor.
  - exact enriched_profunctor_to_whiskered.
  - exact enriched_profunctor_whiskered_bifunctor_weq_left.
  - exact enriched_profunctor_whiskered_bifunctor_weq_right.
Defined.

Definition enriched_profunctor_bifunctor_weq
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
  : enriched_functor
      (tensor_enriched_precat (op_enrichment V E₂) E₁)
      (make_enriched_cat (pr111 V ,, self_enrichment V))
    ≃
    (E₁ ↛e E₂)
  := (enriched_profunctor_whiskered_bifunctor_weq _ _
      ∘ enriched_bifunctor_whiskered_bifunctor_weq _ _ _)%weq.

(** * 4. Action on morphisms in the underlying category *)
Definition lmap_e_arr
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
           (x : C₁)
           {y₁ y₂ : C₂}
           (g : y₂ --> y₁)
  : P y₁ x --> P y₂ x
  := mon_linvunitor _
     · (enriched_from_arr _ g #⊗ identity _)
     · lmap_e P y₁ y₂ x.

Definition rmap_e_arr
           {V : sym_mon_closed_cat}
           {C₁ C₂ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           (P : E₁ ↛e E₂)
           {x₁ x₂ : C₁}
           (f : x₁ --> x₂)
           (y : C₂)
  : P y x₁ --> P y x₂
  := mon_linvunitor _
     · (enriched_from_arr _ f #⊗ identity _)
     · rmap_e P y x₁ x₂.

Proposition lmap_e_arr_id
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            (x : C₁)
            (y : C₂)
  : lmap_e_arr P x (identity y) = identity _.
Proof.
  unfold lmap_e_arr.
  rewrite enriched_from_arr_id.
  rewrite !assoc'.
  rewrite lmap_e_id.
  apply mon_linvunitor_lunitor.
Qed.

Proposition lmap_e_arr_comp
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            (x : C₁)
            {y₁ y₂ y₃ : C₂}
            (g₁ : y₂ --> y₁)
            (g₂ : y₃ --> y₂)
  : lmap_e_arr P x (g₂ · g₁)
    =
    lmap_e_arr P x g₁ · lmap_e_arr P x g₂.
Proof.
  unfold lmap_e_arr.
  rewrite enriched_from_arr_comp.
  rewrite !assoc.
  rewrite tensor_comp_id_r.
  rewrite !assoc'.
  rewrite lmap_e_comp'.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite !assoc'.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_lassociator.
    rewrite !assoc'.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- mon_linvunitor_triangle.
  do 2 apply maponpaths_2.
  rewrite sym_mon_braiding_linvunitor.
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  apply idpath.
Qed.

Proposition rmap_e_arr_id
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            (x : C₁)
            (y : C₂)
  : rmap_e_arr P (identity x) y = identity _.
Proof.
  unfold rmap_e_arr.
  rewrite enriched_from_arr_id.
  rewrite !assoc'.
  rewrite rmap_e_id.
  apply mon_linvunitor_lunitor.
Qed.

Proposition rmap_e_arr_comp
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            {x₁ x₂ x₃ : C₁}
            (f₁ : x₁ --> x₂)
            (f₂ : x₂ --> x₃)
            (y : C₂)
  : rmap_e_arr P (f₁ · f₂) y
    =
    rmap_e_arr P f₁ y · rmap_e_arr P f₂ y.
Proof.
  unfold rmap_e_arr.
  rewrite enriched_from_arr_comp.
  rewrite !assoc.
  rewrite tensor_comp_id_r.
  rewrite !assoc'.
  rewrite rmap_e_comp.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_lassociator.
    rewrite !assoc'.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- mon_linvunitor_triangle.
  apply idpath.
Qed.

Proposition lmap_e_arr_lmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            (x : C₁)
            {y₁ y₂ : C₂}
            (g : y₂ --> y₁)
            (y₃ : C₂)
  : (identity _ #⊗ lmap_e_arr P x g) · lmap_e P y₂ y₃ x
    =
    (postcomp_arr E₂ y₃ g #⊗ identity _) · lmap_e P y₁ y₃ x.
Proof.
  unfold lmap_e_arr.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  rewrite lmap_e_lmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  unfold postcomp_arr.
  rewrite !tensor_comp_id_r.
  apply maponpaths_2.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    rewrite <- tensor_comp_id_r.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_r.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite mon_inv_triangle.
  etrans.
  {
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    apply id_right.
  }
  rewrite <- tensor_comp_id_r.
  rewrite sym_mon_braiding_rinvunitor.
  apply idpath.
Qed.

Proposition rmap_e_arr_lmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            {x₁ x₂ : C₁}
            (f : x₁ --> x₂)
            (y₁ y₂ : C₂)
  : (identity _ #⊗ rmap_e_arr P f y₁) · lmap_e P y₁ y₂ x₂
    =
    lmap_e P y₁ y₂ x₁ · rmap_e_arr P f y₂.
Proof.
  unfold rmap_e_arr.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  rewrite rmap_e_lmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    rewrite <- tensor_split.
    rewrite tensor_split'.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    rewrite tensor_lassociator.
    apply idpath.
  }
  rewrite !assoc.
  rewrite tensor_id_id.
  apply maponpaths_2.
  rewrite mon_inv_triangle.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite mon_lassociator_rassociator.
    rewrite id_left.
    apply idpath.
  }
  rewrite !assoc.
  rewrite <- tensor_comp_id_r.
  rewrite sym_mon_braiding_rinvunitor.
  rewrite mon_linvunitor_triangle.
  apply idpath.
Qed.

Proposition rmap_e_arr_rmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            {x₁ x₂ : C₁}
            (f : x₁ --> x₂)
            (x₃ : C₁)
            (y : C₂)
  : (identity _ #⊗ rmap_e_arr P f y) · rmap_e P y x₂ x₃
    =
    (precomp_arr E₁ x₃ f #⊗ identity _) · rmap_e P y x₁ x₃.
Proof.
  unfold rmap_e_arr.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  rewrite rmap_e_rmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  unfold precomp_arr.
  rewrite !tensor_comp_id_r.
  apply maponpaths_2.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  rewrite tensor_rassociator.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite mon_inv_triangle.
  rewrite !assoc'.
  rewrite mon_lassociator_rassociator.
  apply id_right.
Qed.

Proposition lmap_e_arr_rmap_e
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            (x₁ x₂ : C₁)
            {y₁ y₂ : C₂}
            (f : y₁ --> y₂)
  : (identity _ #⊗ lmap_e_arr P x₁ f) · rmap_e P y₁ x₁ x₂
    =
    rmap_e P y₂ x₁ x₂ · lmap_e_arr P x₂ f.
Proof.
  unfold lmap_e_arr.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  rewrite lmap_e_rmap_e'.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    rewrite <- tensor_split.
    rewrite tensor_split'.
    apply idpath.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_rassociator.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_id_r.
    rewrite tensor_sym_mon_braiding.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    rewrite tensor_lassociator.
    apply idpath.
  }
  rewrite !assoc.
  rewrite tensor_id_id.
  apply maponpaths_2.
  rewrite mon_inv_triangle.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite mon_lassociator_rassociator.
    rewrite id_left.
    apply idpath.
  }
  rewrite !assoc.
  rewrite <- tensor_comp_id_r.
  rewrite sym_mon_braiding_rinvunitor.
  rewrite mon_linvunitor_triangle.
  apply idpath.
Qed.

Proposition lmap_e_arr_rmap_e_arr
            {V : sym_mon_closed_cat}
            {C₁ C₂ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            (P : E₁ ↛e E₂)
            {x₁ x₂ : C₁}
            (f : x₂ --> x₁)
            {y₁ y₂ : C₂}
            (g : y₁ --> y₂)
  : lmap_e_arr P _ g · rmap_e_arr P f _
    =
    rmap_e_arr P f _ · lmap_e_arr P _ g.
Proof.
  unfold lmap_e_arr.
  rewrite !assoc'.
  rewrite <- rmap_e_arr_lmap_e.
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  rewrite <- tensor_split'.
  rewrite tensor_split.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  apply idpath.
Qed.
