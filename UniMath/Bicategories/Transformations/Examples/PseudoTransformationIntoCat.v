(********************************************************************************

 Pseudotransformations and indexed functors

 In this file, we relate indexed functors and pseudotransformations. We first
 give constructors for pseudotransformations between pseudofunctors whose source
 is a discrete bicategory, and in the case that the target is the bicategory of
 univalent categories. After that, we show that every indexed functor gives rise
 to a pseudotransformation and vice versa.

 Contents
 1. Pseudotransformations between pseudofunctors from discrete bicategories
 2. Pseudotransformations between pseudofunctors to categories
 3. Indexed functors to pseudotransformations
 4. Pseudotransformations to indexed functors

 ********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PseudoFunctorsIntoCat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Local Open Scope cat.

(**
 1. Pseudotransformations between pseudofunctors from discrete bicategories
 *)
Section PseudoTransFromCat.
  Context {C : category}
          {B : bicat}
          {F G : psfunctor (cat_to_bicat C) B}
          (τ₀ : ∏ (x : C), F x --> G x)
          (τ₁ : ∏ (x y : C)
                  (f : x --> y),
                invertible_2cell (τ₀ x · # G f) (# F f · τ₀ y))
          (τid : ∏ (x : C),
                 (τ₀ x ◃ psfunctor_id G x)
                 • τ₁ x x (identity x)
                 =
                 runitor (τ₀ x)
                 • linvunitor (τ₀ x)
                 • (psfunctor_id F x ▹ τ₀ x))
          (τc : ∏ (x y z : C)
                  (f : x --> y)
                  (g : y --> z),
                (τ₀ x ◃ psfunctor_comp G f g)
                • τ₁ x z (f · g)
                =
                lassociator (τ₀ x) (# G f) (# G g)
                • (τ₁ x y f ▹ # G g)
                • rassociator (# F f) (τ₀ y) (# G g)
                • (# F f ◃ τ₁ y z g)
                • lassociator (# F f) (# F g) (τ₀ z)
                • (psfunctor_comp F f g ▹ τ₀ z)).

  Definition make_pstrans_from_cat_data
    : pstrans_data F G.
  Proof.
    use make_pstrans_data.
    - exact τ₀.
    - exact τ₁.
  Defined.

  Proposition make_pstrans_from_cat_laws
    : is_pstrans make_pstrans_from_cat_data.
  Proof.
    repeat split.
    - cbn ; intros x y f g p.
      induction p.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (_ @ psfunctor_id2 G f).
        apply maponpaths.
        apply homset_property.
      }
      rewrite lwhisker_id2.
      rewrite id2_left.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        refine (_ @ psfunctor_id2 F f).
        apply maponpaths.
        apply homset_property.
      }
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - exact τid.
    - exact τc.
  Qed.

  Definition make_pstrans_from_cat
    : pstrans F G.
  Proof.
    use make_pstrans.
    - exact make_pstrans_from_cat_data.
    - exact make_pstrans_from_cat_laws.
  Defined.
End PseudoTransFromCat.

(**
 2. Pseudotransformations between pseudofunctors to categories
 *)
Definition pstrans_from_cat_into_cat_data
           {C : category}
           (F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats)
  : UU
  := ∑ (τ₀ : ∏ (x : C), F x --> G x),
     ∏ (x y : C)
       (f : x --> y),
     nat_z_iso (τ₀ x · # G f) (# F f · τ₀ y).

Definition make_pstrans_from_cat_into_cat_data
           {C : category}
           {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
           (τ₀ : ∏ (x : C), F x --> G x)
           (τ₁ : ∏ (x y : C)
                   (f : x --> y),
                 nat_z_iso (τ₀ x · # G f) (# F f · τ₀ y))
  : pstrans_from_cat_into_cat_data F G
  := τ₀ ,, τ₁.

Definition pstrans_from_cat_into_cat_data_to_ob
           {C : category}
           {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
           (τ : pstrans_from_cat_into_cat_data F G)
           (x : C)
  : F x --> G x
  := pr1 τ x.

Coercion pstrans_from_cat_into_cat_data_to_ob : pstrans_from_cat_into_cat_data >-> Funclass.

Definition pstrans_from_cat_into_cat_data_nat
           {C : category}
           {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
           (τ : pstrans_from_cat_into_cat_data F G)
           {x y : C}
           (f : x --> y)
  : nat_z_iso (τ x · # G f) (# F f · τ y)
  := pr2 τ x y f.

Definition pstrans_from_cat_into_cat_laws
           {C : category}
           {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
           (τ : pstrans_from_cat_into_cat_data F G)
  : UU
  := (∏ (x : C)
        (xx : pr1 (F x)),
      pr11 (psfunctor_id G x) (pr1 (τ x) xx)
      · pr1 (pstrans_from_cat_into_cat_data_nat τ (id₁ x)) xx
      =
      # (pr1 (τ x)) (pr11 (psfunctor_id F x) xx))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z)
        (xx : pr1 (F x)),
       pr11 (psfunctor_comp G f g) (pr1 (τ x) xx)
       · pr1 (pstrans_from_cat_into_cat_data_nat τ (f · g)) xx
       =
       # (pr1 (# G g)) ((pr11 (pstrans_from_cat_into_cat_data_nat τ f)) xx)
       · (pr11 (pstrans_from_cat_into_cat_data_nat τ g)) (pr1 (# F f) xx)
       · # (pr1 (τ z)) (pr11 (psfunctor_comp F f g) xx)).

Section PseudoTransIntoCat.
  Context {C : category}
          {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
          (τ : pstrans_from_cat_into_cat_data F G)
          (Hτ : pstrans_from_cat_into_cat_laws τ).

  Definition pstrans_from_cat_into_cat
    : pstrans F G.
  Proof.
    use make_pstrans_from_cat.
    - exact τ.
    - intros x y f.
      use nat_z_iso_to_invertible_2cell.
      exact (pstrans_from_cat_into_cat_data_nat τ f).
    - abstract
        (intros x ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro xx ;
         cbn -[psfunctor_id] ;
         rewrite !id_left ;
         exact (pr1 Hτ x xx)).
    - abstract
        (intros x y z f g ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro xx ;
         cbn -[psfunctor_comp] ;
         rewrite !id_left ;
         rewrite !id_right ;
         exact (pr2 Hτ x y z f g xx)).
  Defined.
End PseudoTransIntoCat.

(**
 3. Indexed functors to pseudotransformations
 *)
Definition indexed_functor_to_pstrans
           {C : category}
           {Φ Ψ : indexed_cat C}
           (τ : indexed_functor Φ Ψ)
  : pstrans
      (indexed_cat_to_psfunctor Φ)
      (indexed_cat_to_psfunctor Ψ).
Proof.
  use pstrans_from_cat_into_cat.
  - use make_pstrans_from_cat_into_cat_data.
    + exact τ.
    + exact (λ x y f, indexed_functor_natural τ f).
  - split.
    + exact (λ x xx, indexed_functor_id τ xx).
    + exact (λ x y z f g xx, indexed_functor_comp τ f g xx).
Defined.

(**
 4. Pseudotransformations to indexed functors
 *)
Section PseudoTransformationToIndexedFunctor.
  Context {C : category}
          {F G : psfunctor (cat_to_bicat C) bicat_of_univ_cats}
          (τ : pstrans F G).

  Definition pstrans_to_indexed_functor_data
    : indexed_functor_data
        (psfunctor_to_indexed_cat F)
        (psfunctor_to_indexed_cat G).
  Proof.
    use make_indexed_functor_data.
    - exact (λ x, τ x).
    - exact (λ x y f, invertible_2cell_to_nat_z_iso _ _ (psnaturality_of τ f)).
  Defined.

  Proposition pstrans_to_indexed_functor_laws
    : indexed_functor_laws pstrans_to_indexed_functor_data.
  Proof.
    repeat split.
    - intros x xx.
      refine (nat_trans_eq_pointwise (pstrans_id τ x) xx @ _) ; cbn.
      rewrite !id_left.
      apply idpath.
    - intros x y z f g xx.
      refine (nat_trans_eq_pointwise (pstrans_comp τ f g) xx @ _) ; cbn.
      rewrite !id_left, !id_right.
      apply idpath.
  Qed.

  Definition pstrans_to_indexed_functor
    : indexed_functor
        (psfunctor_to_indexed_cat F)
        (psfunctor_to_indexed_cat G).
  Proof.
    use make_indexed_functor.
    - exact pstrans_to_indexed_functor_data.
    - exact pstrans_to_indexed_functor_laws.
  Defined.
End PseudoTransformationToIndexedFunctor.
