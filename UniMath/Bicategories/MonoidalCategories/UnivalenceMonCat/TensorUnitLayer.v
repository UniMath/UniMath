(*
This is the third of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct the total category of the (direct) product of the unit and tensor layer. This finishes the first layer.
*)

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.

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
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section TensorUnitLayer.

  Definition bidisp_tensor_unit : disp_bicat _
    := disp_dirprod_bicat bidisp_tensor_disp_bicat bidisp_unit_disp_bicat.

  Definition bidisp_tensorunit_is_disp_univalent_2 : disp_univalent_2 bidisp_tensor_unit.
  Proof.
    apply is_univalent_2_dirprod_bicat.
    - apply univalent_cat_is_univalent_2.
    - apply bidisp_tensor_disp_prebicat_is_univalent_2.
    - apply bidisp_unit_disp_prebicat_is_univalent_2.
  Defined.

  Definition bidisp_tensor_unit_total : bicat := total_bicat bidisp_tensor_unit.

  Definition bidisp_tensorunit_is_univalent_2: is_univalent_2 bidisp_tensor_unit_total.
  Proof.
    apply is_univalent_2_total_dirprod.
    - apply univalent_cat_is_univalent_2.
    - apply bidisp_tensor_disp_prebicat_is_univalent_2.
    - apply bidisp_unit_disp_prebicat_is_univalent_2.
  Defined.

  Definition disp_tensorunit_univalentcat (C : bidisp_tensor_unit_total) : univalent_category
    := pr1 C.

  Definition tensorunit_unit (C : bidisp_tensor_unit_total) : (pr1 C : univalent_category) := pr22 C.

  Definition tensorunit_tensor (C : bidisp_tensor_unit_total) : tensor (pr1 C : univalent_category) := pr12 C.

  Definition tensorunit_preserves_unit {C D : bidisp_tensor_unit_total}
             (F : bidisp_tensor_unit_total⟦C, D⟧)
    : (pr1 D : univalent_category)⟦
          tensorunit_unit D,
          (pr1 F : functor
                     (pr1 C : univalent_category)
                     (pr1 D : univalent_category)) (tensorunit_unit C)
        ⟧ := pr22 F.

  Definition tensorunit_preserves_tensor_data {C D : bidisp_tensor_unit_total}
             (F : bidisp_tensor_unit_total⟦C, D⟧)
    : preserves_tensor_data _ _ (pr1 F : functor _ _) := pr112 F.

  Definition equality_tensor_unit_with_layer (C : bicat_of_univ_cats) :
    bidisp_tensor_unit C = tensor_unit (C : univalent_category).
  Proof.
    apply idpath.
  Defined.

  Definition equality_functor_tensor_unit_with_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuC : bidisp_tensor_unit C)
             (tuD : bidisp_tensor_unit D)
    : tuC -->[F] tuD = functor_tensor_unit tuC tuD F.
  Proof.
    apply idpath.
  Defined.

  Definition tu_cat := bidisp_tensor_unit_total.
  Definition uc (C : tu_cat) : univalent_category := pr1 C.
  Definition tu (C : tu_cat) : tensor_unit (uc C) := pr2 C.
  Definition fuc {C D : tu_cat} (F : tu_cat⟦C,D⟧) : functor (uc C) (uc D) := pr1 F.
  Definition ftu {C D : tu_cat} (F : tu_cat⟦C,D⟧) : functor_tensor_unit (tu C) (tu D) (fuc F)
    := pr2 F.

  Definition bidisp_tensorunit_disp_2cells_isaprop : disp_2cells_isaprop bidisp_tensor_unit.
  Proof.
    apply disp_2cells_isaprop_prod.
    - apply bidisp_tensor_disp_2cells_isaprop.
    - apply bidisp_unit_disp_2cells_isaprop.
  Qed.

  Definition bidisp_tensorunit_disp_locally_groupoid : disp_locally_groupoid bidisp_tensor_unit.
  Proof.
    apply disp_locally_groupoid_prod.
    - apply bidisp_tensor_disp_locally_groupoid.
    - apply bidisp_unit_disp_locally_groupoid.
  Qed.

End TensorUnitLayer.

Module TensorUnitNotations.
  Notation "I_{ C }" := (tensorunit_unit C).
  Notation "T_{ C }" := (tensorunit_tensor C).
  Notation "pu_{ F }" := (tensorunit_preserves_unit F).
  Notation "pt_{ F }" := (tensorunit_preserves_tensor_data F).
  Notation "x ⊗_{ C } y" := (tensor_on_ob T_{C} x y) (at level 31).
  Notation "f ⊗^{ C } g" := (tensor_on_hom T_{C} _ _ _ _ f g) (at level 31).

End TensorUnitNotations.
