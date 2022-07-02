Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Tensorlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Unitlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.TensorUnitlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.leftUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.rightUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.associatorLayer.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

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

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section UnitorsLayers.

  Definition bicatcatsunitors_disp_bicat : disp_bicat _
    := disp_dirprod_bicat bicatcatslu_disp_bicat bicatcatsru_disp_bicat.

  Definition bicatcatsunitors_total : bicat := total_bicat bicatcatsunitors_disp_bicat.

  Definition bicatcatsunitors_disp_prebicat_is_univalent_2
    : disp_univalent_2 bicatcatsunitors_disp_bicat.
  Proof.
    apply is_univalent_2_dirprod_bicat.
    - apply bicatcatstensorunit_is_univalent_2.
    - apply bicatcatslu_disp_prebicat_is_univalent_2.
    - apply bicatcatsru_disp_prebicat_is_univalent_2.
  Qed.

  Definition bicatcatsunitors_is_univalent_2: is_univalent_2 bicatcatsunitors_total.
  Proof.
    apply is_univalent_2_total_dirprod.
    - apply bicatcatstensorunit_is_univalent_2.
    - apply bicatcatslu_disp_prebicat_is_univalent_2.
    - apply bicatcatsru_disp_prebicat_is_univalent_2.
  Qed.

  Definition unitors_tensorunit (C : bicatcatsunitors_total)
    : bicatcatstensorunit_total := pr1 C.

  Definition unitors_leftunitor (C : bicatcatsunitors_total)
    : lunitor_data (pr1 C) := (pr112 C : lunitor_data (pr1 C)).

  Definition unitors_rightunitor (C : bicatcatsunitors_total)
  : runitor_data (pr1 C) := (pr122 C : runitor_data (pr1 C)).

End UnitorsLayers.

Section AssociatorUnitorsLayer.

  Definition bicatcatsassunitors_disp_bicat : disp_bicat _
    := disp_dirprod_bicat bicatcatsunitors_disp_bicat bicatcatsass_disp_bicat.

  Definition bicatcatsassunitors_total : bicat := total_bicat bicatcatsassunitors_disp_bicat.

  Definition bicatcatsassunitors_is_disp_univalent_2
    : disp_univalent_2 bicatcatsassunitors_disp_bicat.
  Proof.
    apply is_univalent_2_dirprod_bicat.
    - apply bicatcatstensorunit_is_univalent_2.
    - apply bicatcatsunitors_disp_prebicat_is_univalent_2.
    - apply bicatcatsass_disp_prebicat_is_univalent_2.
  Qed.

  Definition bicatcatsassunitors_is_univalent_2: is_univalent_2 bicatcatsassunitors_total.
  Proof.
    apply is_univalent_2_total_dirprod.
    - apply bicatcatstensorunit_is_univalent_2.
    - apply bicatcatsunitors_disp_prebicat_is_univalent_2.
    - apply bicatcatsass_disp_prebicat_is_univalent_2.
  Qed.

  Definition assunitors_univcategory (C : bicatcatsassunitors_total)
    : univalent_category := pr11 C.

  Definition assunitors_tensorunit (C : bicatcatsassunitors_total)
    : bicatcatstensorunit_total := pr1 C.

  Definition assunitors_tensor (C : bicatcatsassunitors_total)
    : tensor (pr11 C) := tensorunit_tensor (assunitors_tensorunit C).

  Definition assunitors_unit (C : bicatcatsassunitors_total)
    : ob (pr11 C : univalent_category) := tensorunit_unit (assunitors_tensorunit C).

  Definition assunitors_associator (C : bicatcatsassunitors_total)
    : associator_data (pr1 C) := pr122 C.

  Context {C : bicatcatsassunitors_total}.
  Check pr1 (pr112 C).

  Definition assunitors_leftunitor (C : bicatcatsassunitors_total)
    : lunitor_data (pr1 C) := pr1 (pr112 C).

  Definition assunitors_rightunitor (C : bicatcatsassunitors_total)
    : runitor_data (pr1 C) := pr1 (pr212 C).

End AssociatorUnitorsLayer.

Module AssociatorUnitorsNotations.

  Notation "I_{ C }" := (assunitors_unit C).
  Notation "T_{ C }" := (assunitors_tensor C).
  Notation "x ⊗_{ C } y" := (tensor_on_ob T_{C} x y) (at level 31).
  Notation "f ⊗^{ C } g" := (tensor_on_hom T_{C} _ _ _ _ f g) (at level 31).

  Notation "lu^{ C }" := (assunitors_leftunitor C).
  Notation "ru^{ C }" := (assunitors_rightunitor C).
  Notation "ass^{ C }" := (assunitors_associator C).

End AssociatorUnitorsNotations.
