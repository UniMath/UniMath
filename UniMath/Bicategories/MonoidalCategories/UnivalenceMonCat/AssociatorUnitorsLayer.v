(*
The second displayed layer we lay over the bicategory of univalent categories has the purppose of adding the unitors and the associator. In this file we construct the displayed bicategory which adds all the data of the unitors and the associator.

For example:
The total category corresponding to the displayed layer of the associator is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data (and naturality) of the associator.
- The morphisms express a preservation condition of the associator.
- The 2-cells are trivial.
 *)

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
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import  UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section LeftUnitorLayer.

  Definition disp_lu_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, lunitor (tu C)).
    - exact (λ C D luC luD F, preserves_lunitor (ftu F) luC luD).
  Defined.

  Definition disp_lu_disp_id_comp : disp_cat_id_comp tu_cat disp_lu_disp_ob_mor.
  Proof.
    use tpair.
    - intros C lu.
      apply id_preserves_lunitor.
    - intros C D E F G luC luD luE pluF pluG x.
      apply (comp_preserves_lunitor pluF pluG).
  Defined.


  Definition disp_lu_disp_cat_data : disp_cat_data tu_cat
    := (disp_lu_disp_ob_mor,, disp_lu_disp_id_comp).

  Definition bidisp_lu_disp_bicat : disp_bicat tu_cat
    := disp_cell_unit_bicat disp_lu_disp_cat_data.

  Lemma bidisp_lu_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bidisp_lu_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intro ; intros.
    apply isaprop_preserves_lunitor.
  Qed.

  Lemma isaset_lunitor (C : tu_cat) : isaset (lunitor (pr2 C)).
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

  Lemma isaprop_lunitor_nat (C : tu_cat) (lu : lunitor (pr2 C)) : isaprop (lunitor_nat (pr1 lu)).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

  Lemma bidisp_lu_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bidisp_lu_disp_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_0.
    - apply bidisp_tensorunit_is_univalent_2.
    - intro ; intros.
      apply isaprop_preserves_lunitor.
    - intro ; apply isaset_lunitor.
    - intros C lu1 lu2 plu.
      use total2_paths_f.
      + apply funextsec ; intro.
        refine (_ @ (pr1 plu x)).
        refine (! id_left _ @ _).
        apply cancel_postcomposition.
        refine (_ @ ! id_right _).
        apply (! tensor_id _ _ _).
      + apply isaprop_lunitor_nat.
  Qed.

  Lemma bidisp_lu_disp_prebicat_is_univalent_2 : disp_univalent_2 bidisp_lu_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bidisp_lu_disp_prebicat_is_globally_univalent.
    - apply bidisp_lu_disp_prebicat_is_locally_univalent.
  Defined.

End LeftUnitorLayer.

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

Section UnitorsLayer.

  Definition bidisp_unitors_disp_bicat : disp_bicat tu_cat
    := disp_dirprod_bicat bidisp_lu_disp_bicat bidisp_ru_disp_bicat.

  Definition bidisp_unitors_disp_2cells_isaprop : disp_2cells_isaprop bidisp_unitors_disp_bicat.
  Proof.
    intro ; intros.
    apply isapropdirprod ; apply isapropunit.
  Qed.

  Definition bidisp_lunitor_disp_locally_groupoid : disp_locally_groupoid bidisp_lu_disp_bicat.
  Proof.


    intro ; intros.
    exists tt.
    split ; apply isapropunit.
  Qed.

  Definition bidisp_runitor_disp_locally_groupoid : disp_locally_groupoid bidisp_ru_disp_bicat.
  Proof.
    intro ; intros.
    exists tt.
    split ; apply isapropunit.
  Qed.

  Definition bidisp_unitors_disp_locally_groupoid : disp_locally_groupoid bidisp_unitors_disp_bicat.
  Proof.
    apply disp_locally_groupoid_prod.
    - apply bidisp_lunitor_disp_locally_groupoid.
    - apply bidisp_runitor_disp_locally_groupoid.
  Qed.

End UnitorsLayer.

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

  Definition bidisp_associator_disp_2cells_isaprop : disp_2cells_isaprop bidisp_ass_disp_bicat.
  Proof.
    intro ; intros.
    apply isapropunit.
  Qed.

  Definition bidisp_associator_disp_locally_groupoid : disp_locally_groupoid bidisp_ass_disp_bicat.
  Proof.
    intro ; intros.
    exists tt.
    split ; apply isapropunit.
  Qed.

End AssociatorLayer.

Section AssociatorUnitorsLayer.

  Definition bidisp_assunitors_disp_bicat : disp_bicat tu_cat
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
