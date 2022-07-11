(*
This is the thirth of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct the total category of the (direct) product of the unit and tensor layer. This finishes the first layer.
*)

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Tensorlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Unitlayer.

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section TensorUnitLayer.

  Definition bicatcatstensorunit_total : bicat := total_bicat (disp_dirprod_bicat bicatcatstensor_disp_bicat bicatcatsunit_disp_bicat).

  Definition bicatcatstensorunit_is_univalent_2: is_univalent_2 bicatcatstensorunit_total.
  Proof.
    apply is_univalent_2_total_dirprod.
    - apply univalent_cat_is_univalent_2.
    - apply bicatcatstensor_disp_prebicat_is_univalent_2.
    - apply bicatcatsunit_disp_prebicat_is_univalent_2.
  Defined.

  Definition bicatcatstensorunit_univalentcat (C : bicatcatstensorunit_total) : univalent_category
    := pr1 C.

  Definition tensorunit_unit (C : bicatcatstensorunit_total) : (pr1 C : univalent_category) := pr22 C.

  Definition tensorunit_tensor (C : bicatcatstensorunit_total) : tensor (pr1 C : univalent_category) := pr12 C.

  Definition tensorunit_preserves_unit {C D : bicatcatstensorunit_total}
             (F : bicatcatstensorunit_total⟦C, D⟧)
    : (pr1 D : univalent_category)⟦
          tensorunit_unit D,
          (pr1 F : functor
                     (pr1 C : univalent_category)
                     (pr1 D : univalent_category)) (tensorunit_unit C)
        ⟧ := pr22 F.

  Definition tensorunit_preserves_tensor_data {C D : bicatcatstensorunit_total}
             (F : bicatcatstensorunit_total⟦C, D⟧)
    : preserves_tensor_data _ _ (pr1 F : functor _ _) := pr112 F.



End TensorUnitLayer.

Module TensorUnitNotations.
  Notation "I_{ C }" := (tensorunit_unit C).
  Notation "T_{ C }" := (tensorunit_tensor C).
  Notation "pu_{ F }" := (tensorunit_preserves_unit F).
  Notation "pt_{ F }" := (tensorunit_preserves_tensor_data F).
  Notation "x ⊗_{ C } y" := (tensor_on_ob T_{C} x y) (at level 31).
  Notation "f ⊗^{ C } g" := (tensor_on_hom T_{C} _ _ _ _ f g) (at level 31).

End TensorUnitNotations.
