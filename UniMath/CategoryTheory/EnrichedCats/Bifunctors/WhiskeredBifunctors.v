(******************************************************************************************

 Whiskered bifunctors

 In this file, we define whiskered bifunctors for enriched categories. These represent
 functors from the tensor of two enriched categories to another enriched category. We use
 a whiskered style in this definition meaning that we have a left action and a right action
 rather than a single action.

 Let's be more concrete. In a curried bifunctor, we have for all `x₁ x₂ : C₁` and `y₁ y₂ : C₂`
 a morphism `E₁ ⦃ x₁ , x₂ ⦄ ⊗ (E₂ ⦃ y₁ , y₂ ⦄) --> E₃ ⦃ F x₁ y₁ , F x₂ y₂ ⦄`. For a whiskered
 bifunctor, we split this into two morphisms:
 - a left action `E₁ ⦃ x₁ , x₂ ⦄ --> E₃ ⦃ F x₁ y , F x₂ y ⦄`
 - a right action `E₂ ⦃ y₁ , y₂ ⦄ --> E₃ ⦃ F x y₁ , F x y₂ ⦄`
 The advantage of this definition over the others, is that the laws become simpler. The
 reason for that comes from the composition operation of the tensor of two enriched categories.
 For that operation, we use the so-called `inner_swap` morphism, which gives us a morphism
 from `(E₁ ⦃ x₂, x₃ ⦄ ⊗ (E₂ ⦃ y₂, y₃ ⦄)) ⊗ (E₁ ⦃ x₁, x₂ ⦄ ⊗ (E₂ ⦃ y₁, y₂ ⦄))` to the object
 `(E₁ ⦃ x₂, x₃ ⦄ ⊗ (E₁ ⦃ x₁, x₂ ⦄)) ⊗ (E₂ ⦃ y₂, y₃ ⦄ ⊗ (E₂ ⦃ y₁, y₂ ⦄))` where the two middle
 objects are swapped. This `inner_swap` morphism has a rather complicated definition. By
 using the whiskered style, the laws become much simpler. In the definition of the laws
 ([enriched_whiskered_bifunctor_laws]), one can see that none uses `inner_swap`, and that
 no associators/unitors are present (only one braiding).m

 Contents
 1. Definition of whiskered bifunctors
 2. Accessors for whiskered bifunctors
 3. Equivalence with functors from the tensor

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

(** * 1. Definition of whiskered bifunctors *)
Definition enriched_whiskered_bifunctor_data
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : UU
  := ∑ (F : C₁ → C₂ → C₃),
     (∏ (x₁ x₂ : C₁)
        (y : C₂),
      E₁ ⦃ x₁ , x₂ ⦄
      -->
      E₃ ⦃ F x₁ y , F x₂ y ⦄)
     ×
     (∏ (x : C₁)
        (y₁ y₂ : C₂),
      E₂ ⦃ y₁ , y₂ ⦄
      -->
      E₃ ⦃ F x y₁ , F x y₂ ⦄).

Definition make_enriched_whiskered_bifunctor_data
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : C₁ → C₂ → C₃)
           (Fl : ∏ (x₁ x₂ : C₁)
                   (y : C₂),
                 E₁ ⦃ x₁ , x₂ ⦄
                 -->
                 E₃ ⦃ F x₁ y , F x₂ y ⦄)
           (Fr : ∏ (x : C₁)
                   (y₁ y₂ : C₂),
                 E₂ ⦃ y₁ , y₂ ⦄
                 -->
                 E₃ ⦃ F x y₁ , F x y₂ ⦄)
  : enriched_whiskered_bifunctor_data E₁ E₂ E₃
  := F ,, Fl ,, Fr.

Definition enriched_whiskered_bifunctor_ob
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
           (x : C₁)
           (y : C₂)
  : C₃
  := pr1 F x y.

Coercion enriched_whiskered_bifunctor_ob : enriched_whiskered_bifunctor_data >-> Funclass.

Definition enriched_whiskered_bifunctor_left
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
           (x₁ x₂ : C₁)
           (y : C₂)
  : E₁ ⦃ x₁ , x₂ ⦄
    -->
    E₃ ⦃ F x₁ y , F x₂ y ⦄
  := pr12 F x₁ x₂ y.

Definition enriched_whiskered_bifunctor_right
           {V : monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
           (x : C₁)
           (y₁ y₂ : C₂)
  : E₂ ⦃ y₁ , y₂ ⦄
    -->
    E₃ ⦃ F x y₁ , F x y₂ ⦄
  := pr22 F x y₁ y₂.

Definition enriched_whiskered_bifunctor_laws
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
  : UU
  := (∏ (x : C₁) (y : C₂),
      enriched_id E₁ x · enriched_whiskered_bifunctor_left F x x y
      =
      enriched_id E₃ (F x y))
     ×
     (∏ (x : C₁) (y : C₂),
      enriched_id E₂ y · enriched_whiskered_bifunctor_right F x y y
      =
      enriched_id E₃ (F x y))
     ×
     (∏ (x₁ x₂ x₃ : C₁) (y : C₂),
      enriched_comp E₁ x₁ x₂ x₃ · enriched_whiskered_bifunctor_left F x₁ x₃ y
      =
      (enriched_whiskered_bifunctor_left F x₂ x₃ y
       #⊗
       enriched_whiskered_bifunctor_left F x₁ x₂ y)
      · enriched_comp E₃ (F x₁ y) (F x₂ y) (F x₃ y))
     ×
     (∏ (x : C₁) (y₁ y₂ y₃ : C₂),
      enriched_comp E₂ y₁ y₂ y₃ · enriched_whiskered_bifunctor_right F x y₁ y₃
      =
      (enriched_whiskered_bifunctor_right F x y₂ y₃
       #⊗
       enriched_whiskered_bifunctor_right F x y₁ y₂)
      · enriched_comp E₃ (F x y₁) (F x y₂) (F x y₃))
     ×
     (∏ (x₁ x₂ : C₁) (y₁ y₂ : C₂),
      enriched_whiskered_bifunctor_left F x₁ x₂ y₂
      #⊗
      enriched_whiskered_bifunctor_right F x₁ y₁ y₂
      · enriched_comp _ _ _ _
      =
      sym_mon_braiding V _ _
      ·
      (enriched_whiskered_bifunctor_right F _ _ _
       #⊗
       enriched_whiskered_bifunctor_left F _ _ _)
      · enriched_comp _ _ _ _).

Proposition isaprop_enriched_whiskered_bifunctor_laws
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
  : isaprop (enriched_whiskered_bifunctor_laws F).
Proof.
  repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enriched_whiskered_bifunctor
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : UU
  := ∑ (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃),
     enriched_whiskered_bifunctor_laws F.

Definition make_enriched_whiskered_bifunctor
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_whiskered_bifunctor_data E₁ E₂ E₃)
           (HF : enriched_whiskered_bifunctor_laws F)
  : enriched_whiskered_bifunctor E₁ E₂ E₃
  := F ,, HF.

Coercion enriched_whiskered_bifunctor_to_data
         {V : sym_monoidal_cat}
         {C₁ C₂ C₃ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         {E₃ : enrichment C₃ V}
         (F : enriched_whiskered_bifunctor E₁ E₂ E₃)
  : enriched_whiskered_bifunctor_data E₁ E₂ E₃.
Proof.
  exact (pr1 F).
Defined.

(** * 2. Accessors for whiskered bifunctors *)
Section Accessors.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_whiskered_bifunctor E₁ E₂ E₃).

  Proposition enriched_whiskered_bifunctor_left_id
              (x : C₁)
              (y : C₂)
    : enriched_id E₁ x · enriched_whiskered_bifunctor_left F x x y
      =
      enriched_id E₃ (F x y).
  Proof.
    exact (pr12 F x y).
  Defined.

  Proposition enriched_whiskered_bifunctor_right_id
              (x : C₁)
              (y : C₂)
    : enriched_id E₂ y · enriched_whiskered_bifunctor_right F x y y
      =
      enriched_id E₃ (F x y).
  Proof.
    exact (pr122 F x y).
  Defined.

  Proposition enriched_whiskered_bifunctor_left_comp
              (x₁ x₂ x₃ : C₁)
              (y : C₂)
    : enriched_comp E₁ x₁ x₂ x₃ · enriched_whiskered_bifunctor_left F x₁ x₃ y
      =
      (enriched_whiskered_bifunctor_left F x₂ x₃ y
       #⊗
       enriched_whiskered_bifunctor_left F x₁ x₂ y)
      · enriched_comp E₃ (F x₁ y) (F x₂ y) (F x₃ y).
  Proof.
    exact (pr1 (pr222 F) x₁ x₂ x₃ y).
  Defined.

  Proposition enriched_whiskered_bifunctor_right_comp
              (x : C₁)
              (y₁ y₂ y₃ : C₂)
    : enriched_comp E₂ y₁ y₂ y₃ · enriched_whiskered_bifunctor_right F x y₁ y₃
      =
      (enriched_whiskered_bifunctor_right F x y₂ y₃
       #⊗
       enriched_whiskered_bifunctor_right F x y₁ y₂)
      · enriched_comp E₃ (F x y₁) (F x y₂) (F x y₃).
  Proof.
    exact (pr12 (pr222 F) x y₁ y₂ y₃).
  Defined.

  Proposition enriched_whiskered_bifunctor_left_right
              (x₁ x₂ : C₁)
              (y₁ y₂ : C₂)
    : enriched_whiskered_bifunctor_left F x₁ x₂ y₂
      #⊗
      enriched_whiskered_bifunctor_right F x₁ y₁ y₂
      · enriched_comp _ _ _ _
      =
      sym_mon_braiding V _ _
      ·
      (enriched_whiskered_bifunctor_right F _ _ _
       #⊗
       enriched_whiskered_bifunctor_left F _ _ _)
      · enriched_comp _ _ _ _.
  Proof.
    exact (pr22 (pr222 F) x₁ x₂ y₁ y₂).
  Defined.

  Proposition enriched_whiskered_bifunctor_left_right'
              (x₁ x₂ : C₁)
              (y₁ y₂ : C₂)
    : enriched_whiskered_bifunctor_right F _ _ _
      #⊗
      enriched_whiskered_bifunctor_left F _ _ _
      · enriched_comp _ _ _ _
      =
      sym_mon_braiding V _ _
      · (enriched_whiskered_bifunctor_left F x₁ x₂ y₂
         #⊗
         enriched_whiskered_bifunctor_right F x₁ y₁ y₂)
      · enriched_comp _ _ _ _.
  Proof.
    rewrite !assoc'.
    rewrite enriched_whiskered_bifunctor_left_right.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    rewrite id_left.
    apply idpath.
  Qed.
End Accessors.

(** * 3. Equivalence with functors from the tensor *)
Section FromWhiskeredBifunctor.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_whiskered_bifunctor E₁ E₂ E₃).

  Definition enriched_whiskered_bifunctor_to_curried_data
    : enriched_curried_bifunctor_data E₁ E₂ E₃.
  Proof.
    use make_enriched_curried_bifunctor_data.
    - exact (λ x y, F x y).
    - exact (λ x₁ x₂ y₁ y₂,
             enriched_whiskered_bifunctor_left F x₁ x₂ y₂
             #⊗
             enriched_whiskered_bifunctor_right F x₁ y₁ y₂
             · enriched_comp _ _ _ _).
  Defined.

  Proposition enriched_whiskered_bifunctor_to_curried_laws
    : enriched_curried_bifunctor_laws enriched_whiskered_bifunctor_to_curried_data.
  Proof.
    split.
    - intros x y ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_comp_mor.
        rewrite enriched_whiskered_bifunctor_left_id.
        rewrite enriched_whiskered_bifunctor_right_id.
        apply idpath.
      }
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      apply id_left.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite enriched_whiskered_bifunctor_left_comp.
        rewrite enriched_whiskered_bifunctor_right_comp.
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        apply idpath.
      }
      rewrite !assoc.
      rewrite naturality_inner_swap.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite tensor_split'.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split.
          apply idpath.
        }
        rewrite tensor_comp_mor.
        apply idpath.
      }
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_mor.
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite tensor_split'.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split.
          apply idpath.
        }
        rewrite tensor_comp_mor.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split.
          rewrite !assoc'.
          rewrite enrichment_assoc.
          rewrite !assoc.
          rewrite <- tensor_id_id.
          rewrite tensor_lassociator.
          apply idpath.
        }
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !tensor_comp_id_l.
        apply maponpaths.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        do 2 apply maponpaths_2.
        apply enriched_whiskered_bifunctor_left_right'.
      }
      rewrite !tensor_comp_id_l.
      rewrite !tensor_comp_id_r.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        rewrite <- tensor_comp_id_r.
        rewrite <- tensor_sym_mon_braiding.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite tensor_comp_id_r.
        rewrite !assoc.
        rewrite <- tensor_rassociator.
        apply idpath.
      }
      etrans.
      {
        rewrite !tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      unfold inner_swap.
      rewrite tensor_mor_left, tensor_mor_right.
      rewrite !tensor_comp_id_l.
      rewrite !assoc'.
      do 3 apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        rewrite <- tensor_id_id.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite <- !tensor_comp_id_l.
      apply maponpaths.
      rewrite enrichment_assoc'.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition enriched_whiskered_bifunctor_to_curried
    : enriched_curried_bifunctor E₁ E₂ E₃.
  Proof.
    use make_enriched_curried_bifunctor.
    - exact enriched_whiskered_bifunctor_to_curried_data.
    - exact enriched_whiskered_bifunctor_to_curried_laws.
  Defined.
End FromWhiskeredBifunctor.

Section ToWhiskeredBifunctor.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_curried_bifunctor E₁ E₂ E₃).

  Definition enriched_curried_bifunctor_whiskered_data
    : enriched_whiskered_bifunctor_data E₁ E₂ E₃.
  Proof.
    use make_enriched_whiskered_bifunctor_data.
    - exact (λ x y, F x y).
    - exact (λ x₁ x₂ y,
             mon_rinvunitor _
             · (identity _ #⊗ enriched_id E₂ y)
             · enriched_curried_bifunctor_mor F x₁ x₂ y y).
    - exact (λ x y₁ y₂,
             mon_linvunitor _
             · (enriched_id E₁ x #⊗ identity _)
             · enriched_curried_bifunctor_mor F x x y₁ y₂).
  Defined.

  Proposition enriched_curried_bifunctor_whiskered_laws
    : enriched_whiskered_bifunctor_laws
        enriched_curried_bifunctor_whiskered_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      refine (_ @ enriched_curried_bifunctor_id F _ _).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      rewrite <- tensor_split'.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      apply idpath.
    - intros x y ; cbn.
      refine (_ @ enriched_curried_bifunctor_id F _ _).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      rewrite <- tensor_split.
      apply idpath.
    - intros x₁ x₂ x₃ y ; cbn.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        rewrite <- enriched_curried_bifunctor_comp.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_mor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- naturality_inner_swap.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_id_id.
        rewrite <- tensor_comp_id_l.
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- enrichment_id_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite tensor_lunitor.
        apply idpath.
      }
      rewrite tensor_comp_id_l.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(id_right _) @ _ @ id_left _).
      rewrite <- mon_runitor_rinvunitor.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        refine (_ @ precompose_inner_swap_with_lunitors_and_runitor _ _ _).
        rewrite !assoc'.
        apply maponpaths.
        apply maponpaths_2.
        rewrite tensor_mor_left.
        apply idpath.
      }
      rewrite <- tensor_comp_mor.
      rewrite !mon_rinvunitor_runitor.
      rewrite tensor_id_id.
      apply idpath.
    - intros x y₁ y₂ y₃ ; cbn.
      refine (!_).
      etrans.
      {
        rewrite tensor_comp_mor.
        rewrite !assoc'.
        rewrite <- enriched_curried_bifunctor_comp.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_comp_mor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- naturality_inner_swap.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite tensor_split'.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_id_id.
        rewrite <- tensor_comp_id_r.
        apply maponpaths_2.
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite tensor_runitor.
        apply idpath.
      }
      rewrite tensor_comp_id_r.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(id_right _) @ _ @ id_left _).
      rewrite <- mon_lunitor_linvunitor.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        refine (_ @ precompose_inner_swap_with_lunitors_on_right _ _ _).
        rewrite !assoc'.
        apply maponpaths.
        apply maponpaths_2.
        rewrite tensor_mor_right.
        rewrite mon_runitor_I_mon_lunitor_I.
        apply idpath.
      }
      rewrite <- tensor_comp_mor.
      rewrite !mon_linvunitor_lunitor.
      rewrite tensor_id_id.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ ; cbn.


      rewrite !tensor_comp_mor.
      rewrite !assoc'.
      rewrite <- !enriched_curried_bifunctor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- naturality_inner_swap.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite <- enrichment_id_left.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- naturality_inner_swap.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite <- enrichment_id_left.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- inner_swap_commute_with_swap.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_comp_mor.
      rewrite sym_mon_braiding_runitor.
      rewrite sym_mon_braiding_lunitor.
      apply idpath.
  Qed.

  Definition enriched_curried_bifunctor_whiskered
    : enriched_whiskered_bifunctor E₁ E₂ E₃.
  Proof.
    use make_enriched_whiskered_bifunctor.
    - exact enriched_curried_bifunctor_whiskered_data.
    - exact enriched_curried_bifunctor_whiskered_laws.
  Defined.
End ToWhiskeredBifunctor.

Section Inverses.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}.

  Proposition enriched_whiskered_weq_curried_bifunctor_left
              (F : enriched_whiskered_bifunctor E₁ E₂ E₃)
    : enriched_curried_bifunctor_whiskered (enriched_whiskered_bifunctor_to_curried F)
      =
      F.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enriched_whiskered_bifunctor_laws.
    }
    refine (maponpaths (λ z, pr11 F ,, z) _).
    use pathsdirprod ; cbn.
    - use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite enriched_whiskered_bifunctor_right_id.
        rewrite id_left.
        apply idpath.
      }
      rewrite tensor_split'.
      rewrite !assoc'.
      rewrite <- enrichment_id_right.
      rewrite tensor_runitor.
      rewrite !assoc.
      rewrite mon_rinvunitor_runitor.
      apply id_left.
    - use funextsec ; intro x.
      use funextsec ; intro y₁.
      use funextsec ; intro y₂.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_mor.
        rewrite enriched_whiskered_bifunctor_left_id.
        rewrite id_left.
        apply idpath.
      }
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      apply id_left.
  Qed.

  Proposition enriched_whiskered_weq_curried_bifunctor_right
              (F : enriched_curried_bifunctor E₁ E₂ E₃)
    : enriched_whiskered_bifunctor_to_curried (enriched_curried_bifunctor_whiskered F)
      =
      F.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_enriched_curried_bifunctor_laws.
    }
    refine (maponpaths (λ z, pr11 F ,, z) _).
    use funextsec ; intro x₁.
    use funextsec ; intro x₂.
    use funextsec ; intro y₁.
    use funextsec ; intro y₂.
    cbn.
    rewrite tensor_comp_mor.
    rewrite !assoc'.
    rewrite <- enriched_curried_bifunctor_comp.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite tensor_comp_mor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- naturality_inner_swap.
      rewrite !assoc'.
      rewrite <- tensor_comp_mor.
      rewrite <- enrichment_id_left.
      rewrite <- enrichment_id_right.
      apply idpath.
    }
    rewrite inner_swap_along_unit.
    rewrite id_left.
    rewrite <- tensor_comp_mor.
    rewrite mon_rinvunitor_runitor.
    rewrite mon_linvunitor_lunitor.
    apply tensor_id_id.
  Qed.
End Inverses.

Definition enriched_curried_whiskered_bifunctor_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : enriched_curried_bifunctor E₁ E₂ E₃
    ≃
    enriched_whiskered_bifunctor E₁ E₂ E₃.
Proof.
  use weq_iso.
  - exact enriched_curried_bifunctor_whiskered.
  - exact enriched_whiskered_bifunctor_to_curried.
  - exact enriched_whiskered_weq_curried_bifunctor_right.
  - exact enriched_whiskered_weq_curried_bifunctor_left.
Defined.

Definition enriched_bifunctor_whiskered_bifunctor_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : enriched_functor
      (tensor_enriched_precat E₁ E₂)
      (make_enriched_cat (C₃ ,, E₃))
    ≃
    enriched_whiskered_bifunctor E₁ E₂ E₃
  := (enriched_curried_whiskered_bifunctor_weq E₁ E₂ E₃
      ∘ enriched_bifunctor_curried_bifunctor_weq E₁ E₂ E₃)%weq.
