(*
The second displayed layer we lay over the bicategory of univalent categories has the purppose of adding the unitors and the associator. In this file we construct the displayed bicategory which adds all the data of the associator.
More precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data (and naturality) of the associator.
- The morphisms express a preservation condition of the associator.
- The 2-cells are trivial.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section AssociatorLayer.

  Definition disp_ass_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, associator (tu C)).
    - exact (λ C D αC αD F, preserves_associator (ftu F) αC αD).
  Defined.

  Definition disp_ass_disp_id_comp : disp_cat_id_comp tu_cat disp_ass_disp_ob_mor.
  Proof.
    use tpair.
    - intros C α.
      apply id_preserves_associator.
    - intros C D E F G aC aD aE paF paG x y z.
      apply (comp_preserves_associator paF paG).
  Qed.

  Definition disp_ass_disp_cat_data : disp_cat_data tu_cat
    := (disp_ass_disp_ob_mor,, disp_ass_disp_id_comp).

  Definition bidisp_ass_disp_bicat : disp_bicat tu_cat
    := disp_cell_unit_bicat disp_ass_disp_cat_data.

  Lemma bidisp_ass_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bidisp_ass_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intro ; intros.
    apply isaprop_preserves_associator.
  Qed.

  Lemma isaset_associator (C : tu_cat) : isaset (associator (pr2 C)).
  Proof.
    apply isaset_total2.
    {
      do 3 (apply impred_isaset ; intro).
      apply homset_property.
    }
    intro.
    repeat (apply impred_isaset ; intro).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Lemma isaprop_associator_nat (C : tu_cat) (ass : associator (pr2 C))
    : isaprop (associator_nat (pr1 ass)).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

  Lemma bidisp_ass_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bidisp_ass_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_0.
    - apply bidisp_tensorunit_is_univalent_2.
    - intro ; intros.
      apply isaprop_preserves_associator.
    - intro ; apply isaset_associator.
    - intros C a1 a2 pa.
      use total2_paths_f.
      + apply funextsec ; intro x1 ;
          apply funextsec ; intro x2 ;
          apply funextsec ; intro x3.

        set (p := pr1 pa x1 x2 x3).
        cbn in p.
        unfold identityfunctor_preserves_tensor_data in p.
        rewrite id_right in p.
        rewrite id_right in p.
        rewrite tensor_id in p.
        rewrite id_left in p.
        rewrite tensor_id in p.
        rewrite id_right in p.
        exact p.
      + apply isaprop_associator_nat.
  Qed.

  Lemma bidisp_ass_disp_prebicat_is_univalent_2 : disp_univalent_2 bidisp_ass_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bidisp_ass_disp_prebicat_is_globally_univalent.
    - apply bidisp_ass_disp_prebicat_is_locally_univalent.
  Defined.

End AssociatorLayer.
