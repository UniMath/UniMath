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
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.

Local Open Scope cat.
Local Open Scope double_bicat.

Section LocalUnivalence.
  Context (B : verity_double_bicat).

  Definition hor_locally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_1 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_locally_univalent_verity_double_bicat
    : isaprop hor_locally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  Definition ver_locally_univalent_verity_double_bicat
    : UU
    := is_univalent_2_1 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_locally_univalent_verity_double_bicat
    : isaprop ver_locally_univalent_verity_double_bicat.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  Definition locally_univalent_verity_double_bicat
    : UU
    := hor_locally_univalent_verity_double_bicat
       ×
       ver_locally_univalent_verity_double_bicat.

  Proposition isaprop_locally_univalent_verity_double_bicat
    : isaprop locally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_locally_univalent_verity_double_bicat.
    - exact isaprop_ver_locally_univalent_verity_double_bicat.
  Qed.
End LocalUnivalence.
