(*
This is one file which leads to showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the second displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data of a natural transformation from this category to itself (which will be the right unitor for the monoidal structure).
- The morphisms express a naturality condition.
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

Section RightUnitorLayer.

  Definition disp_ru_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, runitor (tu C)).
    - exact (λ C D ruC ruD F, preserves_runitor (ftu F) ruC ruD).
  Defined.

  Definition disp_ru_disp_id_comp : disp_cat_id_comp tu_cat disp_ru_disp_ob_mor.
  Proof.
    use tpair.
    - intros C ru.
      apply id_preserves_runitor.
    - intros C D E F G ruC ruD ruE pruF pruG x.
      apply (comp_preserves_runitor pruF pruG).
  Defined.

  Definition disp_ru_disp_cat_data : disp_cat_data tu_cat
    := (disp_ru_disp_ob_mor,, disp_ru_disp_id_comp).

  Definition bidisp_ru_disp_bicat : disp_bicat tu_cat
    := disp_cell_unit_bicat disp_ru_disp_cat_data.

  Lemma bidisp_ru_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bidisp_ru_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intro ; intros.
    apply isaprop_preserves_runitor.
  Qed.

  Lemma isaset_runitor (C : tu_cat) : isaset (runitor (pr2 C)).
  Proof.
    apply isaset_total2.
    {
      apply impred_isaset ; intro.
      apply homset_property.
    }
    intro.
    repeat (apply impred_isaset ; intro).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Lemma isaprop_runitor_nat {C : tu_cat} (ru : runitor (pr2 C)) : isaprop (runitor_nat (pr1 ru)).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

  Lemma bidisp_ru_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bidisp_ru_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_0.
    - apply bidisp_tensorunit_is_univalent_2.
    - intro ; intros.
      apply isaprop_preserves_runitor.
    - intro ; apply isaset_runitor.
    - intros C ru1 ru2 pru.
      use total2_paths_f.
      + apply funextsec ; intro.
        refine (_ @ (pr1 pru x)).
        refine (! id_left _ @ _).
        apply cancel_postcomposition.
        refine (_ @ ! id_right _).
        apply (! tensor_id _ _ _).
      + apply isaprop_runitor_nat.
  Qed.

  Lemma bidisp_ru_disp_prebicat_is_univalent_2 : disp_univalent_2 bidisp_ru_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bidisp_ru_disp_prebicat_is_globally_univalent.
    - apply bidisp_ru_disp_prebicat_is_locally_univalent.
  Defined.

End RightUnitorLayer.
