Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.LeftUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.RightUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorLayer.

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section AssociatorUnitorsLayer.

  Definition bidisp_unitors_disp_bicat : disp_bicat _
    := disp_dirprod_bicat bidisp_lu_disp_bicat bidisp_ru_disp_bicat.

  Definition bidisp_unitors_disp_2cells_isaprop : disp_2cells_isaprop bidisp_unitors_disp_bicat.
  Proof.
    intro ; intros.
    apply isapropdirprod.
    - apply isapropunit.
    - apply isapropunit.
  Qed.

  Definition bidisp_lunitor_disp_locally_groupoid : disp_locally_groupoid bidisp_lu_disp_bicat.
  Proof.
    intro ; intros.
    use tpair.
    - exact tt.
    - use tpair.
      + apply isapropunit.
      + apply isapropunit.
  Qed.

  Definition bidisp_runitor_disp_locally_groupoid : disp_locally_groupoid bidisp_ru_disp_bicat.
  Proof.
    intro ; intros.
    use tpair.
    - exact tt.
    - use tpair.
      + apply isapropunit.
      + apply isapropunit.
  Qed.

  Definition bidisp_unitors_disp_locally_groupoid : disp_locally_groupoid bidisp_unitors_disp_bicat.
  Proof.
    apply disp_locally_groupoid_prod.
    - apply bidisp_lunitor_disp_locally_groupoid.
    - apply bidisp_runitor_disp_locally_groupoid.
  Qed.

  Definition bidisp_associator_disp_2cells_isaprop : disp_2cells_isaprop bidisp_ass_disp_bicat.
  Proof.
    intro ; intros.
    apply isapropunit.
  Qed.

  Definition bidisp_associator_disp_locally_groupoid : disp_locally_groupoid bidisp_ass_disp_bicat.
  Proof.
    intro ; intros.
    use tpair.
    - exact tt.
    - use tpair.
      + apply isapropunit.
      + apply isapropunit.
  Qed.

  Definition bidisp_assunitors_disp_bicat : disp_bicat _
    := disp_dirprod_bicat bidisp_unitors_disp_bicat bidisp_ass_disp_bicat.


  Definition bidisp_assunitors_disp_2cells_isaprop : disp_2cells_isaprop bidisp_assunitors_disp_bicat.
  Proof.
    intro ; intros.
    apply isapropdirprod.
    - apply bidisp_unitors_disp_2cells_isaprop.
    - apply bidisp_associator_disp_2cells_isaprop.
  Qed.

  Definition bidisp_assunitors_disp_locally_groupoid : disp_locally_groupoid bidisp_assunitors_disp_bicat.
  Proof.
    apply disp_locally_groupoid_prod.
    - apply bidisp_unitors_disp_locally_groupoid.
    - apply bidisp_associator_disp_locally_groupoid.
  Qed.

  Definition bidisp_unitors_disp_prebicat_is_univalent_2
    : disp_univalent_2 bidisp_unitors_disp_bicat.
  Proof.
    apply is_univalent_2_dirprod_bicat.
    - apply bidisp_tensorunit_is_univalent_2.
    - apply bidisp_lu_disp_prebicat_is_univalent_2.
    - apply bidisp_ru_disp_prebicat_is_univalent_2.
  Qed.

  Definition bidisp_assunitors_is_disp_univalent_2
    : disp_univalent_2 bidisp_assunitors_disp_bicat.
  Proof.
    apply is_univalent_2_dirprod_bicat.
    - apply bidisp_tensorunit_is_univalent_2.
    - apply bidisp_unitors_disp_prebicat_is_univalent_2.
    - apply bidisp_ass_disp_prebicat_is_univalent_2.
  Qed.

  Definition disp_tensor_unit_unitors_associator : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ bidisp_assunitors_disp_bicat.

  Definition disp_tensor_unit_unitors_associator_is_disp_univalent_2
    : disp_univalent_2  disp_tensor_unit_unitors_associator.
  Proof.
    apply sigma_disp_univalent_2_with_props.
    - apply univalent_cat_is_univalent_2.
    - apply bidisp_tensorunit_disp_2cells_isaprop.
    - apply bidisp_assunitors_disp_2cells_isaprop.
    - apply bidisp_tensorunit_is_disp_univalent_2 .
    - apply bidisp_assunitors_is_disp_univalent_2.
    - apply bidisp_tensorunit_disp_locally_groupoid.
    - apply bidisp_assunitors_disp_locally_groupoid.
    - apply bidisp_tensorunit_is_disp_univalent_2.
    - apply bidisp_assunitors_is_disp_univalent_2.
  Qed.

  Lemma disp_tensor_unit_unitors_associator_disp_2cells_isaprop
    : disp_2cells_isaprop disp_tensor_unit_unitors_associator.
  Proof.
    apply disp_2cells_isaprop_sigma.
    - apply bidisp_tensorunit_disp_2cells_isaprop.
    - apply bidisp_assunitors_disp_2cells_isaprop.
  Qed.

  Lemma disp_tensor_unit_unitors_associator_disp_locally_groupoid
    : disp_locally_groupoid disp_tensor_unit_unitors_associator.
  Proof.
    intros C D F G α tuuaC tuuaD ptuuaC ptuuaD ptuuac.
    repeat (use tpair) ; try (exact tt).
    - apply bidisp_tensor_disp_locally_groupoid.
      apply ptuuac.
    - apply bidisp_unit_disp_locally_groupoid.
      apply ptuuac.
    - apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    - apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
  Qed.

  Definition bidisp_assunitors_total : bicat := total_bicat disp_tensor_unit_unitors_associator.

  Definition bidisp_assunitors_is_univalent_2: is_univalent_2 bidisp_assunitors_total.
  Proof.
    apply total_is_univalent_2.
    - apply disp_tensor_unit_unitors_associator_is_disp_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

  Definition assunitors_tensor (C : bidisp_assunitors_total)
    : tensor (pr1 C : univalent_category) := pr112 C.

  Definition assunitors_unit (C : bidisp_assunitors_total)
    : ob (pr1 C : univalent_category) := pr212 C.

  Definition assunitors_leftunitor (C : bidisp_assunitors_total)
    : lunitor_data (pr12 C) := pr11 (pr122 C).

  Definition assunitors_rightunitor (C : bidisp_assunitors_total)
    : runitor_data (pr12 C) := pr12 (pr122 C).

  Definition assunitors_associator (C : bidisp_assunitors_total)
    : associator_data (pr12 C) := pr1 (pr222 C).

  (* We now show that the type of displayed objects and 1-cells is as we expect *)
  Definition assunitors_from_layer (C : bicat_of_univ_cats)
    : disp_tensor_unit_unitors_associator C
      -> tensor_unit_unitors_associator (C : univalent_category).
  Proof.
    intro tuua.
    split with (pr1 tuua).
    repeat split.
    + apply (pr112 tuua).
    + apply (pr212 tuua).
    + apply (pr2 tuua).
  Defined.

  (* Definition assunitors_from_layer (C : bicat_of_univ_cats)
    : disp_tensor_unit_unitors_associator C
      -> ∑ tu : tensor_unit (C : univalent_category), unitors_associator tu.
  Proof.
    intro tuua.
    split with (pr1 tuua).
    repeat split.
    + apply (pr112 tuua).
    + apply (pr212 tuua).
    + apply (pr2 tuua).
  Defined. *)

  Definition assunitors_to_layer (C : bicat_of_univ_cats)
    : tensor_unit_unitors_associator (C : univalent_category)
      -> disp_tensor_unit_unitors_associator C.
  Proof.
    intro tuua.
    split with (pr1 tuua).
    repeat split.
    + apply (pr12 tuua).
    + apply (pr122 tuua).
    + apply (pr222 tuua).
  Defined.

  (* Definition assunitors_to_layer (C : bicat_of_univ_cats)
    : (∑ tu : tensor_unit (C : univalent_category), unitors_associator tu)
      -> disp_tensor_unit_unitors_associator C.
  Proof.
    intro tuua.
    split with (pr1 tuua).
    repeat split.
    + apply (pr12 tuua).
    + apply (pr122 tuua).
    + apply (pr222 tuua).
  Defined. *)

  Definition equality_assunitors_with_layer (C : bicat_of_univ_cats) :
    disp_tensor_unit_unitors_associator C
    ≃ tensor_unit_unitors_associator (C : univalent_category).
  Proof.
    use weq_iso.
    - apply assunitors_from_layer.
    - apply assunitors_to_layer.
    - intro ; apply idpath.
    - intro ; apply idpath.
  Defined.

  Definition functor_assunitors_from_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : tuuaC -->[F] tuuaD
      -> functor_tensor_unit_unitors_associator F
            (assunitors_from_layer C tuuaC) (assunitors_from_layer D tuuaD).
  Proof.
    intro ptuua.
    split with (pr1 ptuua).
    repeat split.
    - apply (pr112 ptuua).
    - apply (pr212 ptuua).
    - apply (pr22 ptuua).
  Defined.

  (*Definition functor_assunitors_from_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : tuuaC -->[F] tuuaD
            -> ∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C tuuaC))
          (pr1 (assunitors_from_layer D tuuaD)) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C tuuaC))
          (pr2 (assunitors_from_layer D tuuaD))
          ftu.
  Proof.
    intro ptuua.
    split with (pr1 ptuua).
    repeat split.
    - apply (pr112 ptuua).
    - apply (pr212 ptuua).
    - apply (pr22 ptuua).
  Defined.*)


  Definition functor_assunitors_to_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : functor_tensor_unit_unitors_associator F (assunitors_from_layer C tuuaC) (assunitors_from_layer D tuuaD) -> tuuaC -->[F] tuuaD.
  Proof.
    intro ptuua.
    split with (pr1 ptuua).
    repeat split.
    - apply (pr12 ptuua).
    - apply (pr122 ptuua).
    - apply (pr222 ptuua).
  Defined.

  (* Definition functor_assunitors_to_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : (∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C tuuaC))
          (pr1 (assunitors_from_layer D tuuaD)) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C tuuaC))
          (pr2 (assunitors_from_layer D tuuaD))
          ftu)
      -> tuuaC -->[F] tuuaD.
  Proof.
    intro ptuua.
    split with (pr1 ptuua).
    repeat split.
    - apply (pr12 ptuua).
    - apply (pr122 ptuua).
    - apply (pr222 ptuua).
  Defined.*)

  Definition equality_functor_assunitors_with_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : tuuaC -->[F] tuuaD
            ≃ functor_tensor_unit_unitors_associator F (assunitors_from_layer C tuuaC) (assunitors_from_layer D tuuaD).
  Proof.
    use weq_iso.
    - apply functor_assunitors_from_layer.
    - apply functor_assunitors_to_layer.
    - apply idpath.
    - apply idpath.
  Defined.

  (* Definition equality_functor_assunitors_with_layer
             (C D : bicat_of_univ_cats) (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_tensor_unit_unitors_associator C)
             (tuuaD : disp_tensor_unit_unitors_associator D)
    : tuuaC -->[F] tuuaD
            ≃ ∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C tuuaC))
          (pr1 (assunitors_from_layer D tuuaD)) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C tuuaC))
          (pr2 (assunitors_from_layer D tuuaD))
          ftu.
  Proof.
    use weq_iso.
    - apply functor_assunitors_from_layer.
    - apply functor_assunitors_to_layer.
    - apply idpath.
    - apply idpath.
  Defined.*)

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
