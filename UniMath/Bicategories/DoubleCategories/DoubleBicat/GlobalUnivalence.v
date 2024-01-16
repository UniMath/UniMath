(*****************************************************************************************

 Global Univalence of Verity Double Bicategories

 In this file, we consider four global univalence conditions for Verity double
 bicategories. These are as follows:
 - The underlying horizontal bicategory is univalent.
 - The underlying vertical bicategory is univalent.
 - Both the underlying horizontal and the vertical bicategories are univalent.
 - The Verity double bicategory is gregarious univalent.
 In this file, we define these different univalence conditions.

 The most general of these univalence conditions is given by gregarious univalence. More
 specifically, suppose that we have a Verity double bicategory `B` that satisfies the
 following conditions:
 - `B` is locally univalent (i.e., the underlying horizontal and vertical bicategories are
   locally univalent).
 - `B` is horizontally globally univalent.
 - The vertical 2-cells in `B` correspond to squares whose horizontal sides are identities.
 Then `B` is also gregarious univalent ([hor_globally_univalent_to_gregarious_univalent]).
 An analogous statement can be proven in the vertical case.

 For many Verity double bicategories, we can also prove the reverse implication. More
 specifically, if we assume that every horizontal adjoint equivalence has a companion pair,
 then we can show that gregarious univalence is equivalent to global horizontal univalence
 ([hor_globally_univalent_weq_gregarious_univalent]). The condition that every horizontal
 adjoint equivalence has a companion pair, is called 'Horizontal invariance' by Grandis
 (Definition 4.1.7 in 'Higher Dimensional Categories, From Double to Multiple Categories'
 by Grandis). As such, for locally univalent horizontally invariant Verity double
 bicategories, horizontal global univalence and gregarious univalence are equivalent.

 Horizontal invariance is common for Verity double bicategories. For example, every
 equipment satisfies this condition. This is because equipments are defined to be the
 Verity double bicategories for which every horizontal 1-cell has a companion and a
 conjoint.

 References:
 - Higher Dimensional Categories, From Double to Multiple Categories
   Marco Grandis

 Contents
 1. Horizontally globally univalent Verity double bicategories
 2. Vertically globally univalent Verity double bicategories
 3. Globally univalent Verity double bicategories
 4. Gregarious univalent Verity double bicategories
 5. Horizontally globally univalent to gregarious univalent
 6. Equivalence of horizontal global univalence and gregarious univalence

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
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairUnique.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairAdjEquiv.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.GregariousEquivalence.

Local Open Scope cat.
Local Open Scope double_bicat.

Section Univalence.
  Context (B : verity_double_bicat).

  (** * 1. Horizontally globally univalent Verity double bicategories *)
  Definition hor_globally_univalent
    : UU
    := is_univalent_2_0 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_globally_univalent
    : isaprop hor_globally_univalent.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  (** 2. Vertically globally univalent Verity double bicategories *)
  Definition ver_globally_univalent
    : UU
    := is_univalent_2_0 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_globally_univalent
    : isaprop ver_globally_univalent.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  (** * 3. Globally univalent Verity double bicategories *)
  Definition globally_univalent_verity_double_bicat
    : UU
    := hor_globally_univalent
       ×
       ver_globally_univalent.

  Proposition isaprop_globally_univalent_verity_double_bicat
    : isaprop globally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_globally_univalent.
    - exact isaprop_ver_globally_univalent.
  Qed.

  (** * 4. Gregarious univalent Verity double bicategories *)
  Definition gregarious_univalent
    : UU
    := ∏ (x y : B), isweq (@id_to_gregarious_equivalence B x y).

  Proposition isaprop_gregarious_univalent
    : isaprop gregarious_univalent.
  Proof.
    do 2 (use impred ; intro).
    apply isapropisweq.
  Qed.

  (** * 5. Horizontally globally univalent to gregarious univalent *)
  Definition hor_globally_univalent_to_gregarious_univalent
             (HB_2_1 : locally_univalent_verity_double_bicat B)
             (HB_2_0 : hor_globally_univalent)
             (H : vertically_saturated B)
    : gregarious_univalent.
  Proof.
    intros x y.
    use weqhomot.
    - refine (weqfibtototal
                _ _
                (hor_left_adjoint_equivalence_weq_gregarious_equivalence _ _ H)
              ∘ make_weq _ (HB_2_0 x y))%weq.
      + apply HB_2_1.
      + use univalent_2_0_weakly_hor_invariant.
        apply HB_2_0.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        use (isofhlevelweqf
               1
               (is_hor_gregarious_equivalence_weq_is_gregarious_equivalence _)).
        apply (isaprop_is_hor_gregarious_equivalence H) ; apply HB_2_1.
      }
      apply idpath.
  Qed.

  (** * 6. Equivalence of horizontal global univalence and gregarious univalence *)
  Definition gregarious_univalent_to_hor_globally_univalent
             (H' : weakly_hor_invariant B)
             (HB_2_1 : locally_univalent_verity_double_bicat B)
             (HB_2_0 : gregarious_univalent)
             (H : vertically_saturated B)
    : hor_globally_univalent.
  Proof.
    intros x y.
    use weqhomot.
    - refine (weqfibtototal
               _ _
               (λ h, invweq
                       (hor_left_adjoint_equivalence_weq_gregarious_equivalence
                          _ _ H h))
             ∘ make_weq _ (HB_2_0 x y))%weq.
      + apply HB_2_1.
      + apply H'.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_left_adjoint_equivalence.
        apply HB_2_1.
      }
      apply idpath.
  Qed.

  Definition hor_globally_univalent_weq_gregarious_univalent
             (H' : weakly_hor_invariant B)
             (HB_2_1 : locally_univalent_verity_double_bicat B)
             (H : vertically_saturated B)
    : hor_globally_univalent
      ≃
      gregarious_univalent.
  Proof.
    use weqimplimpl.
    - exact (λ HB_2_0, hor_globally_univalent_to_gregarious_univalent HB_2_1 HB_2_0 H).
    - exact (λ HB_2_0, gregarious_univalent_to_hor_globally_univalent H' HB_2_1 HB_2_0 H).
    - exact isaprop_hor_globally_univalent.
    - exact isaprop_gregarious_univalent.
  Defined.
End Univalence.
