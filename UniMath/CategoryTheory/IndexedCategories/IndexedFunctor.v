(*************************************************************************

 Indexed functors

 An indexed functor between two indexed categories is the same as a
 pseudonatural transformation between the corresponding pseudofunctors.
 In this file, we formulate this notion only using terminology from
 1-category theory and without referring to bicategories, pseudofunctors,
 and pseudonatural transformations. In addition, we can make one
 simplification in this definition. A pseudonatural transformation has an
 invertible 2-cell witnessing the naturality ([indexed_functor_natural]),
 and this invertible 2-cell must itself also be natural. If we are looking
 at indexed categories, then the source bicategory is actually discrete.
 As such, this second naturality condition follows by path induction.

 Contents
 1. The data of an indexed functor
 2. The laws of an indexed functor
 3. Indexed functors

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.

Local Open Scope cat.

(**
 1. The data of an indexed functor
 *)
Definition indexed_functor_data
           {C : category}
           (Φ Ψ : indexed_cat C)
  : UU
  := ∑ (τ₀ : ∏ (x : C), Φ x ⟶ Ψ x),
     ∏ (x y : C)
       (f : x --> y),
     nat_z_iso
       (τ₀ x ∙ (Ψ $ f))
       ((Φ $ f) ∙ τ₀ y).

Definition make_indexed_functor_data
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ₀ : ∏ (x : C), Φ x ⟶ Ψ x)
           (τ₁ : ∏ (x y : C)
                   (f : x --> y),
                 nat_z_iso
                   (τ₀ x ∙ (Ψ $ f))
                   ((Φ $ f) ∙ τ₀ y))
  : indexed_functor_data Φ Ψ
  := τ₀ ,, τ₁.

Definition indexed_functor_to_functor
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor_data Φ Ψ)
           (x : C)
  : Φ x ⟶ Ψ x
  := pr1 τ x.

Coercion indexed_functor_to_functor : indexed_functor_data >-> Funclass.

Definition indexed_functor_natural
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor_data Φ Ψ)
           {x y : C}
           (f : x --> y)
  : nat_z_iso
      (τ x ∙ (Ψ $ f))
      ((Φ $ f) ∙ τ y)
  := pr2 τ x y f.

Definition indexed_functor_natural_z_iso
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor_data Φ Ψ)
           {x y : C}
           (f : x --> y)
           (xx : Φ x)
  : z_iso ((Ψ $ f) (τ x xx)) (τ y ((Φ $ f) xx))
  := nat_z_iso_pointwise_z_iso
       (indexed_functor_natural τ f)
       xx.

(**
 2. The laws of an indexed functor
 *)
Definition indexed_functor_laws
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor_data Φ Ψ)
  : UU
  := (∏ (x : C)
        (xx : Φ x),
      indexed_cat_id Ψ x (τ x xx)
      · indexed_functor_natural τ (identity x) xx
      =
      # (τ x) (indexed_cat_id Φ x xx))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z)
        (xx : Φ x),
      indexed_cat_comp Ψ f g (τ x xx)
      · indexed_functor_natural τ (f · g) xx
      =
      # (Ψ $ g) (indexed_functor_natural τ f xx)
      · (indexed_functor_natural τ g) ((Φ $ f) xx)
      · # (τ z) (indexed_cat_comp Φ f g xx)).

(**
 3. Indexed functors
 *)
Definition indexed_functor
           {C : category}
           (Φ Ψ : indexed_cat C)
  : UU
  := ∑ (τ : indexed_functor_data Φ Ψ), indexed_functor_laws τ.

Definition make_indexed_functor
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor_data Φ Ψ)
           (Hτ : indexed_functor_laws τ)
  : indexed_functor Φ Ψ
  := τ ,, Hτ.

#[reversible=no] Coercion indexed_functor_to_data
         {C : category}
         {Φ Ψ : indexed_cat C}
         (τ : indexed_functor Φ Ψ)
  : indexed_functor_data Φ Ψ
  := pr1 τ.

Section IndexedFunctorLaws.
  Context {C : category}
          {Φ Ψ : indexed_cat C}
          (τ : indexed_functor Φ Ψ).

  Proposition indexed_functor_id
              {x : C}
              (xx : Φ x)
    : indexed_cat_id Ψ x (τ x xx)
      · indexed_functor_natural τ (identity x) xx
      =
      # (τ x) (indexed_cat_id Φ x xx).
  Proof.
    exact (pr12 τ x xx).
  Qed.

  Proposition indexed_functor_comp
              {x y z : C}
              (f : x --> y)
              (g : y --> z)
              (xx : Φ x)
    : indexed_cat_comp Ψ f g (τ x xx)
      · indexed_functor_natural τ (f · g) xx
      =
      # (Ψ $ g) (indexed_functor_natural τ f xx)
      · (indexed_functor_natural τ g) ((Φ $ f) xx)
      · # (τ z) (indexed_cat_comp Φ f g xx).
  Proof.
    exact (pr22 τ x y z f g xx).
  Qed.
End IndexedFunctorLaws.
