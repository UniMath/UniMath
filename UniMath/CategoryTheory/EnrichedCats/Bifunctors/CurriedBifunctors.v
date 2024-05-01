(******************************************************************************************

 Curried bifunctors

 In this file, we define curried bifunctors for enriched categories. These are functors
 from the tensor of enriched categories to another one. This definition uses a curried
 style to define the function on objects.

 Contents
 1. Curried bifunctors
 2. Accessors
 3. Equivalences with functors from the tensor

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

(** * 1. Curried bifunctors *)
Definition enriched_curried_bifunctor_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : UU
  := ∑ (F : C₁ → C₂ → C₃),
     ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂),
     E₁ ⦃ x₁ , x₂ ⦄ ⊗ (E₂ ⦃ y₁ , y₂ ⦄)
     -->
     E₃ ⦃ F x₁ y₁ , F x₂ y₂ ⦄.

Definition make_enriched_curried_bifunctor_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : C₁ → C₂ → C₃)
           (Fm : ∏ (x₁ x₂ : C₁)
                   (y₁ y₂ : C₂),
                 E₁ ⦃ x₁ , x₂ ⦄ ⊗ (E₂ ⦃ y₁ , y₂ ⦄)
                 -->
                 E₃ ⦃ F x₁ y₁ , F x₂ y₂ ⦄)
  : enriched_curried_bifunctor_data E₁ E₂ E₃
  := F ,, Fm.

Definition enriched_curried_bifunctor_ob
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_curried_bifunctor_data E₁ E₂ E₃)
           (x : C₁)
           (y : C₂)
  : C₃
  := pr1 F x y.

Coercion enriched_curried_bifunctor_ob : enriched_curried_bifunctor_data >-> Funclass.

Definition enriched_curried_bifunctor_mor
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_curried_bifunctor_data E₁ E₂ E₃)
           (x₁ x₂ : C₁)
           (y₁ y₂ : C₂)
  : E₁ ⦃ x₁ , x₂ ⦄ ⊗ (E₂ ⦃ y₁ , y₂ ⦄)
    -->
    E₃ ⦃ F x₁ y₁ , F x₂ y₂ ⦄
  := pr2 F x₁ x₂ y₁ y₂.

Definition enriched_curried_bifunctor_laws
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_curried_bifunctor_data E₁ E₂ E₃)
  : UU
  := (∏ (x : C₁) (y : C₂),
      mon_linvunitor I_{ V}
      · enriched_id E₁ x #⊗ enriched_id E₂ y
      · enriched_curried_bifunctor_mor F x x y y
      =
      enriched_id E₃ (F x y))
     ×
     (∏ (x₁ x₂ x₃ : C₁) (y₁ y₂ y₃ : C₂),
      inner_swap V (E₁ ⦃ x₂, x₃ ⦄) (E₂ ⦃ y₂, y₃ ⦄) (E₁ ⦃ x₁, x₂ ⦄) (E₂ ⦃ y₁, y₂ ⦄)
      · enriched_comp E₁ x₁ x₂ x₃ #⊗ enriched_comp E₂ y₁ y₂ y₃
      · enriched_curried_bifunctor_mor F x₁ x₃ y₁ y₃
      =
      enriched_curried_bifunctor_mor F x₂ x₃ y₂ y₃
      #⊗
      enriched_curried_bifunctor_mor F x₁ x₂ y₁ y₂
      · enriched_comp E₃ (F x₁ y₁) (F x₂ y₂) (F x₃ y₃)).

Proposition isaprop_enriched_curried_bifunctor_laws
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            (F : enriched_curried_bifunctor_data E₁ E₂ E₃)
  : isaprop (enriched_curried_bifunctor_laws F).
Proof.
  use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enriched_curried_bifunctor
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : UU
  := ∑ (F : enriched_curried_bifunctor_data E₁ E₂ E₃),
     enriched_curried_bifunctor_laws F.

Definition make_enriched_curried_bifunctor
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F : enriched_curried_bifunctor_data E₁ E₂ E₃)
           (HF : enriched_curried_bifunctor_laws F)
  : enriched_curried_bifunctor E₁ E₂ E₃
  := F ,, HF.

Coercion enriched_curried_bifunctor_to_data
         {V : sym_monoidal_cat}
         {C₁ C₂ C₃ : category}
         {E₁ : enrichment C₁ V}
         {E₂ : enrichment C₂ V}
         {E₃ : enrichment C₃ V}
         (F : enriched_curried_bifunctor E₁ E₂ E₃)
  : enriched_curried_bifunctor_data E₁ E₂ E₃.
Proof.
  exact (pr1 F).
Defined.

(** * 2. Accessors *)
Section Accessors.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_curried_bifunctor E₁ E₂ E₃).

  Proposition enriched_curried_bifunctor_id
              (x : C₁)
              (y : C₂)
    : mon_linvunitor I_{ V}
      · enriched_id E₁ x #⊗ enriched_id E₂ y
      · enriched_curried_bifunctor_mor F x x y y
      =
      enriched_id E₃ (F x y).
  Proof.
    exact (pr12 F x y).
  Defined.

  Proposition enriched_curried_bifunctor_comp
              (x₁ x₂ x₃ : C₁)
              (y₁ y₂ y₃ : C₂)
    : inner_swap V (E₁ ⦃ x₂, x₃ ⦄) (E₂ ⦃ y₂, y₃ ⦄) (E₁ ⦃ x₁, x₂ ⦄) (E₂ ⦃ y₁, y₂ ⦄)
      · enriched_comp E₁ x₁ x₂ x₃ #⊗ enriched_comp E₂ y₁ y₂ y₃
      · enriched_curried_bifunctor_mor F x₁ x₃ y₁ y₃
      =
      enriched_curried_bifunctor_mor F x₂ x₃ y₂ y₃
      #⊗
      enriched_curried_bifunctor_mor F x₁ x₂ y₁ y₂
      · enriched_comp E₃ (F x₁ y₁) (F x₂ y₂) (F x₃ y₃).
  Proof.
    exact (pr22 F x₁ x₂ x₃ y₁ y₂ y₃).
  Defined.
End Accessors.

(** * 3. Equivalences with functors from the tensor *)
Section FromBifunctor.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_curried_bifunctor E₁ E₂ E₃).

  Definition enriched_curried_bifunctor_to_bifunctor_data
    : enriched_functor_data
        (tensor_enriched_precat E₁ E₂)
        (make_enriched_cat (C₃ ,, E₃)).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy, F (pr1 xy) (pr2 xy)).
    - exact (λ xy₁ xy₂, enriched_curried_bifunctor_mor F _ _ _ _).
  Defined.

  Proposition enriched_curried_bifunctor_to_bifunctor_unit_ax
    : enriched_functor_unit_ax
        enriched_curried_bifunctor_to_bifunctor_data.
  Proof.
    intros xy.
    apply enriched_curried_bifunctor_id.
  Defined.

  Proposition enriched_curried_bifunctor_to_bifunctor_comp_ax
    : enriched_functor_comp_ax
        enriched_curried_bifunctor_to_bifunctor_data.
  Proof.
    intros xy₁ xy₂ xy₃.
    apply enriched_curried_bifunctor_comp.
  Defined.

  Definition enriched_curried_bifunctor_to_bifunctor
    : enriched_functor
        (tensor_enriched_precat E₁ E₂)
        (make_enriched_cat (C₃ ,, E₃)).
  Proof.
    simple refine (_ ,, _).
    - exact enriched_curried_bifunctor_to_bifunctor_data.
    - split.
      + exact enriched_curried_bifunctor_to_bifunctor_unit_ax.
      + exact enriched_curried_bifunctor_to_bifunctor_comp_ax.
  Defined.
End FromBifunctor.

Section ToBifunctor.
  Context {V : sym_monoidal_cat}
          {C₁ C₂ C₃ : category}
          {E₁ : enrichment C₁ V}
          {E₂ : enrichment C₂ V}
          {E₃ : enrichment C₃ V}
          (F : enriched_functor
                 (tensor_enriched_precat E₁ E₂)
                 (make_enriched_cat (C₃ ,, E₃))).

  Definition enriched_bifunctor_to_curried_bifunctor_data
    : enriched_curried_bifunctor_data E₁ E₂ E₃.
  Proof.
    use make_enriched_curried_bifunctor_data.
    - exact (λ x y, F (x ,, y)).
    - exact (λ x₁ x₂ y₁ y₂, enriched_functor_on_morphisms F (x₁ ,, y₁) (x₂ ,, y₂)).
  Defined.

  Proposition enriched_bifunctor_to_curried_bifunctor_laws
    : enriched_curried_bifunctor_laws
        enriched_bifunctor_to_curried_bifunctor_data.
  Proof.
    split.
    - intros x y.
      exact (pr12 F (x ,, y)).
    - intros x₁ x₂ x₃ y₁ y₂ y₃.
      exact (pr22 F (x₁ ,, y₁) (x₂ ,, y₂) (x₃ ,, y₃)).
  Defined.

  Definition enriched_bifunctor_to_curried_bifunctor
    : enriched_curried_bifunctor E₁ E₂ E₃.
  Proof.
    use make_enriched_curried_bifunctor.
    - exact enriched_bifunctor_to_curried_bifunctor_data.
    - exact enriched_bifunctor_to_curried_bifunctor_laws.
  Defined.
End ToBifunctor.

Definition enriched_bifunctor_curried_bifunctor_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           (E₁ : enrichment C₁ V)
           (E₂ : enrichment C₂ V)
           (E₃ : enrichment C₃ V)
  : enriched_functor
      (tensor_enriched_precat E₁ E₂)
      (make_enriched_cat (C₃ ,, E₃))
    ≃
    enriched_curried_bifunctor E₁ E₂ E₃.
Proof.
  use weq_iso.
  - exact enriched_bifunctor_to_curried_bifunctor.
  - exact enriched_curried_bifunctor_to_bifunctor.
  - abstract
      (intro F ;
       apply idpath).
  - abstract
      (intro F ;
       apply idpath).
Defined.
