(*****************************************************************************************


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
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.GregariousEquivalence.

Local Open Scope cat.
Local Open Scope double_bicat.

Section Univalence.
  Context (B : verity_double_bicat).

  Definition hor_globally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_0 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_globally_univalent_verity_double_bicat
    : isaprop hor_globally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  Definition ver_globally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_0 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_globally_univalent_verity_double_bicat
    : isaprop ver_globally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_0.
  Qed.

  Definition globally_univalent_verity_double_bicat
    : UU
    := hor_globally_univalent_verity_double_bicat
       ×
       ver_globally_univalent_verity_double_bicat.

  Proposition isaprop_globally_univalent_verity_double_bicat
    : isaprop globally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_globally_univalent_verity_double_bicat.
    - exact isaprop_ver_globally_univalent_verity_double_bicat.
  Qed.

  Definition gregarious_univalent_verity_double_bicat
    : UU
    := ∏ (x y : B), isweq (@id_to_gregarious_equivalence B x y).

  Proposition isaprop_gregarious_univalent_verity_double_bicat
    : isaprop gregarious_univalent_verity_double_bicat.
  Proof.
    do 2 (use impred ; intro).
    apply isapropisweq.
  Qed.

  Definition hor_globally_univalent_to_gregarious_univalent
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
             (HB : hor_globally_univalent_verity_double_bicat)
      : gregarious_univalent_verity_double_bicat.
  Proof.
    intros x y.
    use weqhomot.
    - refine (weqfibtototal
                _ _
                (hor_left_adjoint_equivalence_weq_gregarious_equivalence HB_2_1 HB_2_1' _ H)
              ∘ make_weq _ (HB x y))%weq.
      use univalent_2_0_all_equivs_companions.
      apply HB.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply (isaprop_is_hor_gregarious_equivalence H HB_2_1 HB_2_1').
      }
      apply idpath.
  Qed.

  Definition gregarious_univalent_to_hor_globally_univalent
             (H' : all_equivs_companions B)
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
             (HB : gregarious_univalent_verity_double_bicat)
    : hor_globally_univalent_verity_double_bicat.
  Proof.
    intros x y.
    use weqhomot.
    - exact (weqfibtototal
               _ _
               (λ h, invweq
                       (hor_left_adjoint_equivalence_weq_gregarious_equivalence
                          HB_2_1 HB_2_1' H' H h))
             ∘ make_weq _ (HB x y))%weq.
      - intro p.
        induction p.
        use subtypePath.
        {
          intro.
          apply isaprop_left_adjoint_equivalence.
          exact HB_2_1.
        }
        apply idpath.
    Qed.

  Definition hor_globally_univalent_weq_gregarious_univalent
             (H' : all_equivs_companions B)
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : vertical_cells_are_squares B)
    : hor_globally_univalent_verity_double_bicat
      ≃
      gregarious_univalent_verity_double_bicat.
  Proof.
    use weqimplimpl.
    - exact (hor_globally_univalent_to_gregarious_univalent HB_2_1 HB_2_1' H).
    - exact (gregarious_univalent_to_hor_globally_univalent H' HB_2_1 HB_2_1' H).
    - exact isaprop_hor_globally_univalent_verity_double_bicat.
    - exact isaprop_gregarious_univalent_verity_double_bicat.
  Defined.
End Univalence.
