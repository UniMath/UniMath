(*****************************************************************************************

 Gregarious equivalence

 In this file, we define gregarious equivalences and we establish basic facts about them.
 A gregarious equivalence is a companion pair whose horizontal and vertical morphisms are
 both adjoint equivalences.

 One of the applications of gregarious equivalences is defining gregarious univalent
 Verity double bicategories. For that purpose, we show that the identity is necessarily a
 gregarious equivalence ([id_is_gregarious_equivalence]). In addition, one theorem that we
 are interested in, relates gregarious univalence to the global univalence of the
 horizontal bicategory. For that purpose, we define when a horizontal 1-cell is a gregarious
 equivalence ([is_hor_gregarious_equivalence]) as follows: the 1-cell has a companion pair
 with which it forms a gregarious equivalence. We use this notion to relate horizontal
 adjoint equivalences and gregarious equivalences. More specifically, whenever a Verity
 double bicategory `B` satisfies the following conditions:
 - It is locally univalent.
 - All horizontal equivalences have companion pairs.
 - The vertical 2-cells correspond with squares that have horizontal identity sides.
 Then the type of adjoint equivalences and the type of gregarious equivalences are actually
 equivalent ([hor_left_adjoint_equivalence_weq_gregarious_equivalence]).

 Note that the condition that every horizontal equivalence has a companion pair, is called
 'horizontal invariance' in "Higher Dimensional Categories, From Double to Multiple
 Categories" by Grandis (Definition 4.1.7).

 References:
 - Higher Dimensional Categories, From Double to Multiple Categories
   Marco Grandis

 Contents
 1. Gregarious equivalences
 2. The identity is a gregarious equivalence
 3. Identities to gregarious equivalences
 4. Horizontal gregarious equivalences
 5. Being a horizontal gregarious equivalence is a proposition
 6. Adjoint equivalences and gregarious equivalences

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairUnique.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairAdjEquiv.

Local Open Scope cat.
Local Open Scope double_bicat.

Section GregariousEquivalence.
  Context {B : verity_double_bicat}.

  (** * 1. Gregarious equivalences *)
  Definition is_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
    : UU
    := are_companions h v
       ×
       left_adjoint_equivalence h
       ×
       left_adjoint_equivalence v.

  Coercion is_gregarious_equivalence_to_are_companions
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (H : is_gregarious_equivalence h v)
    : are_companions h v
    := pr1 H.

  Definition gregarious_equivalence
             (x y : B)
    : UU
    := ∑ (h : x --> y)
         (v : x -|-> y),
       is_gregarious_equivalence h v.

  Definition make_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (H : is_gregarious_equivalence h v)
    : gregarious_equivalence x y
    := h ,, v ,, H.

  (** * 2. The identity is a gregarious equivalence *)
  Definition id_is_gregarious_equivalence
             (x : B)
    : is_gregarious_equivalence (id_h x) (id_v x).
  Proof.
    repeat split.
    - apply id_are_companions.
    - apply internal_adjoint_equivalence_identity.
    - apply internal_adjoint_equivalence_identity.
  Defined.

  Definition id_gregarious_equivalence
             (x : B)
    : gregarious_equivalence x x.
  Proof.
    use make_gregarious_equivalence.
    - apply id_h.
    - apply id_v.
    - apply id_is_gregarious_equivalence.
  Defined.

  (** * 3. Identities to gregarious equivalences *)
  Definition id_to_gregarious_equivalence
             {x y : B}
             (p : x = y)
    : gregarious_equivalence x y.
  Proof.
    induction p.
    exact (id_gregarious_equivalence x).
  Defined.

  (** * 4. Horizontal gregarious equivalences *)
  Definition is_hor_gregarious_equivalence
             {x y : B}
             (h : x --> y)
    : UU
    := left_adjoint_equivalence h × ∑ (c : hor_companion h), left_adjoint_equivalence c.

  Definition make_is_hor_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (c : are_companions h v)
             (Hh : left_adjoint_equivalence h)
             (Hv : left_adjoint_equivalence v)
    : is_hor_gregarious_equivalence h
    := Hh ,, (v ,, c) ,, Hv.

  Coercion is_hor_gregarious_equivalence_to_mor
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : hor_companion h
    := pr12 v.

  Coercion is_hor_gregarious_equivalence_to_is_left_adjoint_equivalence
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : left_adjoint_equivalence v
    := pr22 v.

  Definition is_hor_gregarious_equivalence_weq_is_gregarious_equivalence
             {x y : B}
             (h : x --> y)
    : is_hor_gregarious_equivalence h
      ≃
      (∑ (v : x -|-> y), is_gregarious_equivalence h v).
  Proof.
    use weq_iso.
    - exact (λ v, pr112 v ,, pr212 v ,, pr1 v ,, pr22 v).
    - intros v.
      use make_is_hor_gregarious_equivalence.
      + exact (pr1 v).
      + apply (pr2 v).
      + apply (pr2 v).
      + apply (pr2 v).
    - abstract
        (intro ; cbn ;
         apply idpath).
    - abstract
        (intro ; cbn ;
         apply idpath).
  Defined.

  (** * 5. Being a horizontal gregarious equivalence is a proposition *)
  Lemma path_is_hor_gregarious_equivalence
        (H : vertically_saturated B)
        (HB_2_1 : locally_univalent_verity_double_bicat B)
        {x y : B}
        {h : x --> y}
        (φ₁ φ₂ : is_hor_gregarious_equivalence h)
        (p : (φ₁ : x -|-> y) = φ₂)
        (q₁ : lunitor _ ▿s (linvunitor _ ▵s v_sq_idtoiso_2_1 p ⋆h unit_are_companions φ₂)
              =
              unit_are_companions φ₁)
        (q₂ : runitor _ ▿s (linvunitor _ ▵s counit_are_companions φ₁ ⋆h v_sq_idtoiso_2_1 p)
              =
              counit_are_companions φ₂)
    : φ₁ = φ₂.
  Proof.
    use pathsdirprod.
    - apply isaprop_left_adjoint_equivalence.
      apply HB_2_1.
    - use subtypePath.
      {
        intro.
        apply isaprop_left_adjoint_equivalence.
        apply HB_2_1.
      }
      exact (eq_companion_of_hor H HB_2_1 p q₁ q₂).
  Qed.

  Proposition isaprop_is_hor_gregarious_equivalence
              (H : vertically_saturated B)
              (HB_2_1 : locally_univalent_verity_double_bicat B)
              {x y : B}
              (h : x --> y)
    : isaprop (is_hor_gregarious_equivalence h).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use (path_is_hor_gregarious_equivalence H HB_2_1).
    - use (v_sq_isotoid_2_1 H HB_2_1).
      use make_invertible_vertical_square.
      + use make_invertible_vertical_square_data.
        * use (square_between_companions φ₁).
          apply (pr12 φ₂).
        * use (square_between_companions φ₂).
          apply (pr12 φ₁).
      + split.
        * apply comp_square_between_companions.
        * apply comp_square_between_companions.
    - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
      apply square_between_companions_unit.
    - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
      apply square_between_companions_counit.
  Qed.

  (** * 6. Adjoint equivalences and gregarious equivalences *)
  Definition hor_left_adjoint_equivalence_to_gregarious_equivalence
             (H : vertically_saturated B)
             (H' : weakly_hor_invariant B)
             {x y : B}
             (h : x --> y)
             (Hh : left_adjoint_equivalence h)
    : is_hor_gregarious_equivalence h.
  Proof.
    pose (c := H' _ _ h Hh).
    induction c as [ v c ].
    use make_is_hor_gregarious_equivalence.
    - exact v.
    - exact c.
    - exact Hh.
    - use all_equivs_companions_adjequiv.
      + exact H.
      + exact H'.
      + exact h.
      + exact c.
      + exact Hh.
  Qed.

  Definition hor_gregarious_equivalence_to_left_adjoint_equivalence
             {x y : B}
             (h : x --> y)
             (Hh : is_hor_gregarious_equivalence h)
    : left_adjoint_equivalence h.
  Proof.
    apply Hh.
  Qed.

  Definition hor_left_adjoint_equivalence_weq_hor_gregarious_equivalence
             (HB_2_1 : locally_univalent_verity_double_bicat B)
             (H : weakly_hor_invariant B)
             (H' : vertically_saturated B)
             {x y : B}
             (h : x --> y)
    : left_adjoint_equivalence h ≃ is_hor_gregarious_equivalence h.
  Proof.
    use weqimplimpl.
    - apply (hor_left_adjoint_equivalence_to_gregarious_equivalence H' H).
    - apply hor_gregarious_equivalence_to_left_adjoint_equivalence.
    - apply isaprop_left_adjoint_equivalence.
      apply HB_2_1.
    - apply (isaprop_is_hor_gregarious_equivalence H' HB_2_1).
  Qed.

  Definition hor_left_adjoint_equivalence_weq_gregarious_equivalence
             (HB_2_1 : locally_univalent_verity_double_bicat B)
             (H : weakly_hor_invariant B)
             (H' : vertically_saturated B)
             {x y : B}
             (h : x --> y)
    : left_adjoint_equivalence h ≃ ∑ (v : x -|-> y), is_gregarious_equivalence h v
    := (is_hor_gregarious_equivalence_weq_is_gregarious_equivalence h
        ∘ hor_left_adjoint_equivalence_weq_hor_gregarious_equivalence HB_2_1 H H' h)%weq.
End GregariousEquivalence.
