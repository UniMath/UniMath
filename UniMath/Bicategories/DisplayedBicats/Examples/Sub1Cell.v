Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.

Section Sub1CellBicategory.
  Context (B : bicat)
          (P : ∏ (x y : B), x --> y -> UU)
          (Pid : ∏ (x : B), P _ _ (id₁ x))
          (Pcomp : ∏ (x y z : B) (f : x --> y) (g : y --> z),
                   P  _ _ f -> P _ _ g -> P _ _ (f · g)).

  Definition disp_sub1cell_disp_cat
    : disp_cat_ob_mor B.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ _, unit).
    - exact (λ _ _ _ _ f, P _ _ f).
  Defined.

  Definition disp_sub1cell_disp_cat_id_comp
    : disp_cat_id_comp _ disp_sub1cell_disp_cat.
  Proof.
    use tpair.
    - exact (λ _ _, Pid _).
    - exact (λ _ _ _ _ _ _ _ _ p q, Pcomp _ _ _ _ _ p q).
  Defined.

  Definition disp_sub1cell_disp_cat_data
    : disp_cat_data B.
  Proof.
    use tpair.
    - exact disp_sub1cell_disp_cat.
    - exact disp_sub1cell_disp_cat_id_comp.
  Defined.

  Definition disp_sub1cell_prebicat : disp_prebicat B
    := disp_cell_unit_bicat disp_sub1cell_disp_cat_data.

  Definition disp_sub1cell_bicat : disp_bicat B
    := disp_cell_unit_bicat disp_sub1cell_disp_cat_data.

  Definition disp_sub1cell_univalent_2_1
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : disp_univalent_2_1 disp_sub1cell_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply HP.
  Defined.

  Definition disp_sub1cell_univalent_2_0
             (HB : is_univalent_2_1 B)
             (HP : ∏ (x y : B) (f : x --> y), isaprop (P _ _ f))
    : disp_univalent_2_0 disp_sub1cell_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - exact HB.
    - intros ; apply HP.
    - simpl ; intro.
      apply isasetunit.
    - simpl.
      intros.
      apply isapropunit.
  Qed.
End Sub1CellBicategory.
