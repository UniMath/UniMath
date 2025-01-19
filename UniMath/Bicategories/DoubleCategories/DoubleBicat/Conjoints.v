(*****************************************************************************************

 Conjoints

 In this file, we define conjoints in Verity double bicategories (see Definition 4.1.2 in
 "Higher Dimensional Categories, From Double to Multiple Categories" by Grandis). The key
 idea behind the formalization in this file is that this notion is dual to the notion of
 companion pairs. For this reason, we can obtain results about conjoints by instantiating
 results about companion pairs to the horizontal dual of a Verity double bicategory.

 References:
 - Higher Dimensional Categories, From Double to Multiple Categories
   Marco Grandis

 Contents
 1. Definition of conjoints
 2. Conjoints and companions
 3. Identity conjoints
 4. Composition of companion pairs
 5. Verity double bicategories with all conjoints

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairUnique.
Require Import UniMath.Bicategories.DoubleCategories.Examples.HorizontalDual.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Definition of conjoints *)
Definition are_conjoints
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
           (v : y -|-> x)
  : UU
  := ∑ (η : square_double_bicat h (id_h x) (id_v x) v)
       (ε : square_double_bicat (id_h y) h v (id_v y)),
     (rinvunitor _ ◃s (lunitor _ ▹s ε ⋆v η) = id_h_square_bicat _)
     ×
     (lunitor _ ▿s (rinvunitor _ ▵s (η ⋆h ε)) = id_v_square_bicat _).

Definition make_are_conjoints
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
           (v : y -|-> x)
           (η : square_double_bicat h (id_h x) (id_v x) v)
           (ε : square_double_bicat (id_h y) h v (id_v y))
           (p : rinvunitor _ ◃s (lunitor _ ▹s ε ⋆v η) = id_h_square_bicat _)
           (q : lunitor _ ▿s (rinvunitor _ ▵s (η ⋆h ε)) = id_v_square_bicat _)
  : are_conjoints h v
  := η ,, ε ,, p ,, q.

Definition unit_are_conjoints
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : y -|-> x}
           (c : are_conjoints h v)
  : square_double_bicat h (id_h x) (id_v x) v
  := pr1 c.

Definition counit_are_conjoints
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : y -|-> x}
           (c : are_conjoints h v)
  : square_double_bicat (id_h y) h v (id_v y)
  := pr12 c.

Proposition are_conjoints_left
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : y -|-> x}
            (c : are_conjoints h v)
  : rinvunitor _ ◃s (lunitor _ ▹s counit_are_conjoints c ⋆v unit_are_conjoints c)
    =
    id_h_square_bicat _.
Proof.
  exact (pr122 c).
Defined.

Proposition are_conjoints_left'
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : y -|-> x}
            (c : are_conjoints h v)
  : counit_are_conjoints c ⋆v unit_are_conjoints c
    =
    linvunitor _ ▹s (runitor _ ◃s id_h_square_bicat _).
Proof.
  rewrite <- (are_conjoints_left c).
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite lwhisker_square_id.
  rewrite <- rwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition are_conjoints_right
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : y -|-> x}
            (c : are_conjoints h v)
  : lunitor _ ▿s (rinvunitor _ ▵s (unit_are_conjoints c ⋆h counit_are_conjoints c))
    =
    id_v_square_bicat _.
Proof.
  exact (pr222 c).
Defined.

Proposition are_conjoints_right'
            {B : verity_double_bicat}
            {x y : B}
            {h : x --> y}
            {v : y -|-> x}
            (c : are_conjoints h v)
  : unit_are_conjoints c ⋆h counit_are_conjoints c
    =
    linvunitor _ ▿s (runitor _ ▵s id_v_square_bicat _).
Proof.
  rewrite <- (are_conjoints_right c).
  rewrite !dwhisker_uwhisker_square.
  rewrite <- uwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite uwhisker_square_id.
  rewrite <- dwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

(** * 2. Conjoints and companions *)
Definition conjoints_to_dual_companion
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : y -|-> x}
           (c : are_conjoints h v)
  : are_companions (B := horizontal_dual_verity_double_bicat B) h v.
Proof.
  use make_are_companions.
  - exact (unit_are_conjoints c).
  - exact (counit_are_conjoints c).
  - exact (are_conjoints_left c).
  - exact (are_conjoints_right c).
Defined.

Definition conjoints_from_dual_companion
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v : y -|-> x}
           (c : are_companions (B := horizontal_dual_verity_double_bicat B) h v)
  : are_conjoints h v.
Proof.
  use make_are_conjoints.
  - exact (unit_are_companions c).
  - exact (counit_are_companions c).
  - exact (are_companions_left c).
  - exact (are_companions_right c).
Defined.

Definition conjoints_are_dual_companion
           {B : verity_double_bicat}
           {x y : B}
           (h : x --> y)
           (v : y -|-> x)
  : are_conjoints h v
    ≃
    are_companions (B := horizontal_dual_verity_double_bicat B) h v.
Proof.
  use weq_iso.
  - exact conjoints_to_dual_companion.
  - exact conjoints_from_dual_companion.
  - abstract
      (intro ;
       apply idpath).
  - abstract
      (intro ;
       apply idpath).
Defined.

(** * 3. Identity conjoints *)
Definition id_are_conjoints
           {B : verity_double_bicat}
           (x : B)
  : are_conjoints (id_h x) (id_v x).
Proof.
  exact (id_are_companions (B := horizontal_dual_verity_double_bicat B) x).
Defined.

(** * 4. Composition of companion pairs *)
Definition comp_are_conjoints
           {B : verity_double_bicat}
           {x y z : B}
           {h₁ : x --> y}
           {h₂ : y --> z}
           {v₁ : y -|-> x}
           {v₂ : z -|-> y}
           (c₁ : are_conjoints h₁ v₁)
           (c₂ : are_conjoints h₂ v₂)
  : are_conjoints (h₁ · h₂) (v₂ · v₁).
Proof.
  exact (comp_are_companions
           (B := horizontal_dual_verity_double_bicat B)
           c₂ c₁).
Defined.

(** * 5. Verity double bicategories with all conjoints *)
Definition all_conjoints
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y),
     ∑ (v : y -|-> x), are_conjoints h v.

Proposition isaprop_all_conjoints
            (B : verity_double_bicat)
            (H : vertically_saturated B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
  : isaprop (all_conjoints B).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro h.
  apply (isaprop_companion_pair (B := horizontal_dual_verity_double_bicat B)).
  - use horizontal_dual_vertically_saturated.
    exact H.
  - use locally_univalent_horizontal_dual.
    exact HB_2_1.
Qed.
