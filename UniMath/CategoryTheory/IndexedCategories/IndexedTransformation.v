(*************************************************************************

 Indexed transformations

 An indexed natural transformation is the same as a modification between
 two pseudonatural transformations. In this file, we formulate this notion
 using only terminology from 1-category theory. Note that no
 simplifications are made compared to the original definition.

 Contents
 1. The data of an indexed natural transformation
 2. The law of an indexed natural transformation
 3. Indexed natural transformations

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.

Local Open Scope cat.

(**
 1. The data of an indexed natural transformation
 *)
Definition indexed_nat_trans_data
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ θ : indexed_functor Φ Ψ)
  : UU
  := ∏ (x : C), τ x ⟹ θ x.

(**
 2. The law of an indexed natural transformation
 *)
Definition indexed_nat_trans_law
           {C : category}
           {Φ Ψ : indexed_cat C}
           {τ θ : indexed_functor Φ Ψ}
           (m : indexed_nat_trans_data τ θ)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (xx : Φ x),
     indexed_functor_natural τ f xx · m y ((Φ $ f) xx)
     =
     # (Ψ $ f) (m x xx) · indexed_functor_natural θ f xx.

(**
 3. Indexed natural transformations
 *)
Definition indexed_nat_trans
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ θ : indexed_functor Φ Ψ)
  : UU
  := ∑ (m : indexed_nat_trans_data τ θ), indexed_nat_trans_law m.

Definition make_indexed_nat_trans
           {C : category}
           {Φ Ψ : indexed_cat C}
           {τ θ : indexed_functor Φ Ψ}
           (m : indexed_nat_trans_data τ θ)
           (Hm : indexed_nat_trans_law m)
  : indexed_nat_trans τ θ
  := m ,, Hm.

Definition indexed_nat_trans_to_data
           {C : category}
           {Φ Ψ : indexed_cat C}
           {τ θ : indexed_functor Φ Ψ}
           (m : indexed_nat_trans τ θ)
           (x : C)
  : τ x ⟹ θ x
  := pr1 m x.

Coercion indexed_nat_trans_to_data : indexed_nat_trans >-> Funclass.

Proposition indexed_nat_trans_natural
            {C : category}
            {Φ Ψ : indexed_cat C}
            {τ θ : indexed_functor Φ Ψ}
            (m : indexed_nat_trans τ θ)
            {x y : C}
            (f : x --> y)
            (xx : Φ x)
  : indexed_functor_natural τ f xx · m y ((Φ $ f) xx)
    =
    # (Ψ $ f) (m x xx) · indexed_functor_natural θ f xx.
Proof.
  exact (pr2 m x y f xx).
Qed.

Proposition indexed_nat_trans_natural_inv
            {C : category}
            {Φ Ψ : indexed_cat C}
            {τ θ : indexed_functor Φ Ψ}
            (m : indexed_nat_trans τ θ)
            {x y : C}
            (f : x --> y)
            (xx : Φ x)
  : m y ((Φ $ f) xx) · inv_from_z_iso (indexed_functor_natural_z_iso θ f xx)
    =
    inv_from_z_iso (indexed_functor_natural_z_iso τ f xx) · # (Ψ $ f) (m x xx).
Proof.
  refine (!_).
  use z_iso_inv_on_right.
  rewrite !assoc.
  use z_iso_inv_on_left.
  exact (indexed_nat_trans_natural m f xx).
Qed.
