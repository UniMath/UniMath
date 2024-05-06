(******************************************************************************************

 Curried transformations between bifunctors

 We are also interested in transformations between bifunctors. Since in applications we use
 whiskered bifunctors, we also would like to define transformations between bifunctors in a
 whiskered style. For that reason, we first define curried transformations between curried
 bifunctors.

 Contents
 1. Curried transformations between bifunctors
 2. Equivalence with enriched natural transformations

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.EnrichmentEquiv.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.Tensor.
Require Import UniMath.CategoryTheory.EnrichedCats.Bifunctors.CurriedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

(** * 1. Curried transformations between bifunctors *)
Definition curried_enriched_transformation_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_curried_bifunctor E₁ E₂ E₃)
  : UU
  := ∏ (x : C₁) (y : C₂), F x y --> G x y.

Definition curried_enriched_transformation_law
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation_data F G)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂),
     enriched_curried_bifunctor_mor F x₁ x₂ y₁ y₂
     · postcomp_arr _ _ (τ x₂ y₂)
     =
     enriched_curried_bifunctor_mor G x₁ x₂ y₁ y₂
     · precomp_arr _ _ (τ x₁ y₁).

Proposition isaprop_curried_enriched_transformation_law
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_curried_bifunctor E₁ E₂ E₃}
            (τ : curried_enriched_transformation_data F G)
  : isaprop (curried_enriched_transformation_law τ).
Proof.
  do 4 (use impred ; intro).
  apply homset_property.
Qed.

Definition curried_enriched_transformation
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_curried_bifunctor E₁ E₂ E₃)
  : UU
  := ∑ (τ : curried_enriched_transformation_data F G),
     curried_enriched_transformation_law τ.

Definition make_curried_enriched_transformation
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation_data F G)
           (Hτ : curried_enriched_transformation_law τ)
  : curried_enriched_transformation F G
  := τ ,, Hτ.

Definition curried_enriched_transformation_ob
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation F G)
           (x : C₁)
           (y : C₂)
  : F x y --> G x y
  := pr1 τ x y.

Coercion curried_enriched_transformation_ob
  : curried_enriched_transformation >-> Funclass.

Proposition curried_enriched_transformation_natural
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_curried_bifunctor E₁ E₂ E₃}
            (τ : curried_enriched_transformation F G)
            (x₁ x₂ : C₁)
            (y₁ y₂ : C₂)
  : enriched_curried_bifunctor_mor F x₁ x₂ y₁ y₂
    · postcomp_arr _ _ (τ x₂ y₂)
    =
    enriched_curried_bifunctor_mor G x₁ x₂ y₁ y₂
    · precomp_arr _ _ (τ x₁ y₁).
Proof.
  exact (pr2 τ x₁ x₂ y₁ y₂).
Defined.

Proposition eq_curried_enriched_transformation
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_curried_bifunctor E₁ E₂ E₃}
            {τ θ : curried_enriched_transformation F G}
            (p : ∏ (x : C₁) (y : C₂), τ x y = θ x y)
  : τ = θ.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_curried_enriched_transformation_law.
  }
  use funextsec ; intro x.
  use funextsec ; intro y.
  exact (p x y).
Qed.

(** * 2. Equivalence with enriched natural transformations *)
Definition curried_enriched_transformation_to_nat_trans
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : curried_enriched_transformation F G)
  : enriched_nat_trans
      (enriched_curried_bifunctor_to_bifunctor F)
      (enriched_curried_bifunctor_to_bifunctor G).
Proof.
  simple refine (_ ,, _).
  - exact (λ xy, enriched_from_arr _ (τ (pr1 xy) (pr2 xy))).
  - abstract
      (intros xy₁ xy₂ ;
       exact (curried_enriched_transformation_natural
                τ
                (pr1 xy₁) (pr1 xy₂) (pr2 xy₁) (pr2 xy₂))).
Defined.

Definition enriched_nat_trans_to_curried_data
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : enriched_nat_trans
                  (enriched_curried_bifunctor_to_bifunctor F)
                  (enriched_curried_bifunctor_to_bifunctor G))
  : curried_enriched_transformation_data F G
  := λ x y, enriched_to_arr _ (τ (x ,, y)).

Arguments enriched_nat_trans_to_curried_data {V C₁ C₂ C₃ E₁ E₂ E₃ F G} τ /.

Proposition enriched_nat_trans_to_curried_law
            {V : sym_monoidal_cat}
            {C₁ C₂ C₃ : category}
            {E₁ : enrichment C₁ V}
            {E₂ : enrichment C₂ V}
            {E₃ : enrichment C₃ V}
            {F G : enriched_curried_bifunctor E₁ E₂ E₃}
            (τ : enriched_nat_trans
                   (enriched_curried_bifunctor_to_bifunctor F)
                   (enriched_curried_bifunctor_to_bifunctor G))
  : curried_enriched_transformation_law (enriched_nat_trans_to_curried_data τ).
Proof.
  intros x₁ x₂ y₁ y₂.
  refine (_ @ pr2 τ (x₁ ,, y₁) (x₂ ,, y₂) @ _) ; cbn.
  - unfold postcomp_arr, postcompose_underlying_morphism ; cbn.
    rewrite enriched_from_to_arr.
    apply idpath.
  - unfold precomp_arr, precompose_underlying_morphism ; cbn.
    rewrite enriched_from_to_arr.
    apply idpath.
Qed.

Definition enriched_nat_trans_to_curried
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           {F G : enriched_curried_bifunctor E₁ E₂ E₃}
           (τ : enriched_nat_trans
                  (enriched_curried_bifunctor_to_bifunctor F)
                  (enriched_curried_bifunctor_to_bifunctor G))
  : curried_enriched_transformation F G.
Proof.
  use make_curried_enriched_transformation.
  - exact (enriched_nat_trans_to_curried_data τ).
  - exact (enriched_nat_trans_to_curried_law τ).
Defined.

Definition enriched_nat_trans_curried_weq
           {V : sym_monoidal_cat}
           {C₁ C₂ C₃ : category}
           {E₁ : enrichment C₁ V}
           {E₂ : enrichment C₂ V}
           {E₃ : enrichment C₃ V}
           (F G : enriched_curried_bifunctor E₁ E₂ E₃)
  : enriched_nat_trans
      (enriched_curried_bifunctor_to_bifunctor F)
      (enriched_curried_bifunctor_to_bifunctor G)
    ≃
    curried_enriched_transformation F G.
Proof.
  use weq_iso.
  - exact enriched_nat_trans_to_curried.
  - exact curried_enriched_transformation_to_nat_trans.
  - abstract
      (intros τ ;
       use subtypePath ;
       [ intro ; repeat (use impred ; intro) ; apply homset_property | ] ;
       use funextsec ;
       intro xy ; cbn ;
       apply enriched_from_to_arr).
  - abstract
      (intros τ ;
       use eq_curried_enriched_transformation ;
       intros x y ; cbn ;
       apply enriched_to_from_arr).
Defined.
