(*
This is the last file which concludes that the bicategory of univalent monoidal categories is again univalent.
In this file we conclude that both the bicategory of univalent monoidal categories with lax monoidal functors is univalent
and that the result still holds when we replace lax by strong monoidal functors.
*)

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.LeftUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.RightUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorUnitorsLayer.

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import AssociatorUnitorsNotations.

Section LaxLayer.

  Definition bicat_univlaxmon_noprop : bicat := total_bicat disp_tensor_unit_unitors_associator.

  Definition P_triangle_pentagon : bicat_univlaxmon_noprop -> UU
    :=  λ C : bicat_univlaxmon_noprop,
        triangle_pentagon (pr2 (assunitors_from_layer (uc (pr1 C,, pr12 C))  (pr2 C))).

  Definition disp_bicat_univlaxmon : disp_bicat bicat_univlaxmon_noprop
    := disp_fullsubbicat bicat_univlaxmon_noprop P_triangle_pentagon.

  Lemma disp_bicat_univlaxmon_is_univalent_2 : disp_univalent_2 disp_bicat_univlaxmon.
  Proof.
    split.
    - apply disp_univalent_2_0_fullsubbicat.
      + apply bidisp_assunitors_is_univalent_2.
      + intro ; apply isaprop_triangle_pentagon.
    - apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Definition disp_univlaxmon : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ disp_bicat_univlaxmon.

  Definition disp_univlaxmon_is_univalent_2
    : disp_univalent_2 disp_univlaxmon.
  Proof.
    apply sigma_disp_univalent_2_with_props.
    - apply univalent_cat_is_univalent_2.
    - apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_tensor_unit_unitors_associator_is_disp_univalent_2.
    - apply disp_fullsubbicat_univalent_2_1.
    - apply disp_tensor_unit_unitors_associator_disp_locally_groupoid.
    - apply disp_locally_groupoid_fullsubbicat.
    - apply disp_tensor_unit_unitors_associator_is_disp_univalent_2.
    - apply disp_bicat_univlaxmon_is_univalent_2.
  Qed.

  Lemma disp_univlaxmon_disp_2cells_isaprop :  disp_2cells_isaprop disp_univlaxmon.
  Proof.
    apply disp_2cells_isaprop_sigma.
    + apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    + apply disp_2cells_isaprop_fullsubbicat.
  Qed.

  Lemma disp_univlaxmon_disp_locally_groupoid :  disp_locally_groupoid disp_univlaxmon.
  Proof.
    apply disp_locally_groupoid_sigma.
    - apply univalent_cat_is_univalent_2.
    - apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_tensor_unit_unitors_associator_disp_locally_groupoid.
    - apply disp_locally_groupoid_fullsubbicat.
  Qed.

  Definition bicat_univlaxmon : bicat := total_bicat disp_univlaxmon.

  Definition bicat_univlaxmon_is_univalent_2 : is_univalent_2 bicat_univlaxmon.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univlaxmon_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

  (* We now show that the type of displayed objects and 1-cells is as we expect *)
  Definition laxmon_from_layer (C : bicat_of_univ_cats)
    : disp_univlaxmon C
      -> laxmon (C : univalent_category).
  Proof.
    intro M.
    use tpair.
    - apply assunitors_from_layer.
      apply M.
    - apply (pr2 M).
  Defined.

  Definition laxmon_to_layer (C : bicat_of_univ_cats)
    : laxmon (C : univalent_category) → disp_univlaxmon C.
  Proof.
    intro M.
    use tpair.
    - apply assunitors_to_layer.
      apply M.
    - apply (pr2 M).
  Defined.

  Definition equivalence_laxmon_with_layer (C : bicat_of_univ_cats) :
    disp_univlaxmon C ≃ laxmon (C : univalent_category).
  Proof.
    use weq_iso.
    - apply laxmon_from_layer.
    - apply laxmon_to_layer.
    - intro ; apply idpath.
    - intro ; apply idpath.
  Defined.

  Lemma equivalence_oblaxmon_oblayer
    : ob bicat_univlaxmon ≃ ∑ C : bicat_of_univ_cats, laxmon (C : univalent_category).
  Proof.
    apply weqfibtototal.
    intro ; apply equivalence_laxmon_with_layer.
  Defined.

  Definition functor_laxmon_from_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univlaxmon C)
             (tuuaD : disp_univlaxmon D)
    : tuuaC -->[F] tuuaD
            -> functor_tensor_unit_unitors_associator F (assunitors_from_layer C (pr1 tuuaC)) (assunitors_from_layer D (pr1 tuuaD)).
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_assunitors_with_layer.
      apply (pr1 ptuua).
    - repeat (use tpair).
      + apply (pr121 ptuua).
      + apply (pr2 (pr121 ptuua)).
      + apply (pr221 ptuua).
  Defined.

  Definition functor_laxmon_to_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univlaxmon C)
             (tuuaD : disp_univlaxmon D)
    : functor_tensor_unit_unitors_associator F (assunitors_from_layer C (pr1 tuuaC)) (assunitors_from_layer D (pr1 tuuaD)) -> tuuaC -->[F] tuuaD.
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_assunitors_with_layer.
      apply ptuua.
    - exact tt.
  Defined.

  Definition equality_functor_laxmon_with_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univlaxmon C)
             (tuuaD : disp_univlaxmon D)
    : tuuaC -->[F] tuuaD
            ≃ functor_tensor_unit_unitors_associator F (assunitors_from_layer C (pr1 tuuaC)) (assunitors_from_layer D (pr1 tuuaD)).
  Proof.
    use weq_iso.
    - apply functor_laxmon_from_layer.
    - apply functor_laxmon_to_layer.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + apply isapropunit.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + apply idpath_transportf.
  Defined.

End LaxLayer.

Section StrongMonoidalCatLayer.

  Definition P_sass : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,
        strong_associator (pr2 (assunitors_from_layer (pr1 C)  (pr12 C))).

   Definition P_slu : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,
        strong_lunitor (pr2 (assunitors_from_layer (pr1 C)  (pr12 C))).

    Definition P_sru : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,
        strong_runitor (pr2 (assunitors_from_layer (pr1 C)  (pr12 C))).

  Definition P_strong : bicat_univlaxmon -> UU
    := λ C : bicat_univlaxmon, P_sass C × P_slu C × P_sru C.

  Definition disp_bicat_univstrongmon : disp_bicat bicat_univlaxmon
    := disp_fullsubbicat bicat_univlaxmon P_strong.

  Lemma disp_bicat_univstrongmon_is_univalent_2
    : disp_univalent_2 disp_bicat_univstrongmon.
  Proof.
    split.
    - apply disp_univalent_2_0_fullsubbicat.
      + apply bicat_univlaxmon_is_univalent_2.
      + intro.
        repeat (apply isapropdirprod).
        * apply isaprop_strong_associator.
        * apply isaprop_strong_lunitor.
        * apply isaprop_strong_runitor.
    - apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Definition disp_univstrongmon : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ disp_bicat_univstrongmon.

  Definition disp_univstrongmon_is_univalent_2
    : disp_univalent_2 disp_univstrongmon.
  Proof.
    apply sigma_disp_univalent_2_with_props.
    - apply univalent_cat_is_univalent_2.
    - apply disp_univlaxmon_disp_2cells_isaprop.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_univlaxmon_is_univalent_2.
    - apply disp_fullsubbicat_univalent_2_1.
    - apply disp_univlaxmon_disp_locally_groupoid.
    - apply disp_locally_groupoid_fullsubbicat.
    - apply disp_univlaxmon_is_univalent_2.
    - apply disp_bicat_univstrongmon_is_univalent_2.
  Qed.

  Definition bicat_univstrongmon : bicat := total_bicat disp_univstrongmon.

  Definition bicat_univstrongmon_is_univalent_2 : is_univalent_2 bicat_univstrongmon.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univstrongmon_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

  (* We now show that the type of displayed objects and 1-cells is as we expect *)
  Definition strongmon_from_layer (C : bicat_of_univ_cats)
    : disp_univstrongmon C -> strongmon (C : univalent_category).
  Proof.
    intro M.
    use tpair.
    - apply laxmon_from_layer.
      apply (pr1 M).
    - use tpair.
      + apply (pr21 M).
      + repeat (use tpair) ; repeat (apply (pr2 M)).
  Defined.

  Definition strongmon_to_layer (C : bicat_of_univ_cats)
    : strongmon (C : univalent_category)  → disp_univstrongmon C.
  Proof.
    intro M.
    use tpair.
    - apply (laxmon_to_layer _ (strongmon_to_laxmon M)).
    - repeat split.
      + apply (pr2 (pr222 M)).
      + apply (pr122 M).
      + apply (pr1 (pr222 M)).
  Defined.

  Definition equivalence_strongmon_with_layer (C : bicat_of_univ_cats) :
    disp_univstrongmon C ≃  strongmon (C : univalent_category).
  Proof.
    use weq_iso.
    - apply strongmon_from_layer.
    - apply strongmon_to_layer.
    - intro ; apply idpath.
    - intro ; apply idpath.
  Defined.

  Lemma equivalence_obstrongmon_oblayer
    : ob bicat_univstrongmon ≃ ∑ C : bicat_of_univ_cats, strongmon (C : univalent_category).
  Proof.
    apply weqfibtototal.
    intro ; apply equivalence_strongmon_with_layer.
  Defined.

  Definition functor_strongmon_from_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongmon C)
             (tuuaD : disp_univstrongmon D)
    : tuuaC -->[F] tuuaD
            -> ∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C (pr11 tuuaC)))
          (pr1 (assunitors_from_layer D (pr11 tuuaD))) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C (pr11 tuuaC)))
          (pr2 (assunitors_from_layer D (pr11 tuuaD)))
          ftu.
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_laxmon_with_layer.
      apply (pr1 ptuua).
    - repeat (use tpair) ; repeat (apply (pr211 ptuua)).
  Defined.

  Definition functor_strongmon_to_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongmon C)
             (tuuaD : disp_univstrongmon D)
    : (∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C (pr11 tuuaC)))
          (pr1 (assunitors_from_layer D (pr11 tuuaD))) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C (pr11 tuuaC)))
          (pr2 (assunitors_from_layer D (pr11 tuuaD)))
          ftu) -> tuuaC -->[F] tuuaD.
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_laxmon_with_layer.
      apply ptuua.
    - exact tt.
  Defined.

  Definition equality_functor_strongmon_with_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongmon C)
             (tuuaD : disp_univstrongmon D)
    : tuuaC -->[F] tuuaD
            ≃ ∑ ftu : functor_tensor_unit (pr1 (assunitors_from_layer C (pr11 tuuaC)))
          (pr1 (assunitors_from_layer D (pr11 tuuaD))) F,
        functor_unitors_associator
          (pr2 (assunitors_from_layer C (pr11 tuuaC)))
          (pr2 (assunitors_from_layer D (pr11 tuuaD)))
          ftu.
  Proof.
    use weq_iso.
    - apply functor_strongmon_from_layer.
    - apply functor_strongmon_to_layer.
    - intro.
      use total2_paths_f.
      + use total2_paths_f.
        * apply idpath.
        * apply isapropunit.
      + apply isapropunit.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + apply idpath_transportf.
  Defined.

End StrongMonoidalCatLayer.

Section StrongMonoidalFunctorLayer.

  Definition P_strong_preserving : ∏ (C D : bicat_univlaxmon), bicat_univlaxmon⟦C,D⟧ -> UU.
  Proof.
    intros C D F.
    use functor_strong.
    - exact (pr1 C : univalent_category).
    - exact (pr1 D : univalent_category).
    - apply C.
    - apply D.
    - repeat split.
      + exact (pr11 (pr212 C)).
      + exact (pr21 (pr212 C)).
      + exact (pr2 (pr212 C)).
    - repeat split.
      + exact (pr11 (pr212 D)).
      + exact (pr21 (pr212 D)).
      + exact (pr2 (pr212 D)).
    - exact (pr1 F).
    - exact (pr112 F).
    - repeat split ; repeat (apply (pr212 F)).
  Defined.

  Lemma isaprop_P_strong_preserving {C D : bicat_univlaxmon} (F : bicat_univlaxmon⟦C,D⟧)
    : isaprop (P_strong_preserving C D F).
  Proof.
    apply isapropdirprod.
    - apply isaprop_is_z_isomorphism.
    - repeat (apply impred_isaprop ; intro).
      apply isaprop_is_z_isomorphism.
  Qed.

  Import Bicat.Notations.

  Definition Pid_strong_preserving :
    ∏ (C : bicat_univlaxmon), P_strong_preserving _ _ (id₁ C).
  Proof.
    intro C.
    use tpair.
    - apply identity_is_z_iso.
    - intro ; intro.
      apply identity_is_z_iso.
  Defined. (* Should I make this into a Qed? *)

  Definition Pcomp_strong_preserving :
    ∏ (C D E : bicat_univlaxmon) (F : bicat_univlaxmon⟦C,D⟧) (G : bicat_univlaxmon⟦D,E⟧),
      P_strong_preserving _ _ F → P_strong_preserving _ _ G -> P_strong_preserving _ _ (F·G).
  Proof.
    intros C D E F G sF sG.
    use tpair.
    - apply is_z_isomorphism_comp.
      + apply sG.
      + apply functor_on_is_z_isomorphism.
        apply sF.
    - intro ; intro.
      apply is_z_isomorphism_comp.
      + apply sG.
      + simpl.
        apply functor_on_is_z_isomorphism.
        apply sF.
  Defined.

  Definition disp_bicat_univstrongfunctor : disp_bicat bicat_univlaxmon
    := disp_sub1cell_bicat bicat_univlaxmon P_strong_preserving Pid_strong_preserving Pcomp_strong_preserving.

  Definition disp_bicat_univstrongfunctor_is_univalent_2 : disp_univalent_2 disp_bicat_univstrongfunctor.
  Proof.
    apply disp_sub1cell_univalent_2.
    - apply bicat_univlaxmon_is_univalent_2.
    - intro ; intros.
      apply isaprop_P_strong_preserving.
  Qed.

  Definition disp_univstrongfunctor : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ disp_bicat_univstrongfunctor.

  Lemma disp_univstrongfunctor_disp_2cells_isaprop : disp_2cells_isaprop disp_bicat_univstrongfunctor.
  Proof.
    apply disp_2cells_isaprop_sub1cell_bicat.
  Qed.

  Lemma disp_univstrongfunctor_disp_locally_groupoid : disp_locally_groupoid disp_bicat_univstrongfunctor.
  Proof.
    apply disp_locally_groupoid_sub1cell_bicat.
  Qed.

  Definition disp_univstrongfunctor_is_univalent_2
    : disp_univalent_2 disp_univstrongfunctor.
  Proof.
    apply sigma_disp_univalent_2_with_props.
    - apply univalent_cat_is_univalent_2.
    - apply disp_univlaxmon_disp_2cells_isaprop.
    - apply disp_univstrongfunctor_disp_2cells_isaprop.
    - apply disp_univlaxmon_is_univalent_2.
    - apply disp_bicat_univstrongfunctor_is_univalent_2.
    - apply disp_univlaxmon_disp_locally_groupoid.
    - apply disp_univstrongfunctor_disp_locally_groupoid.
    - apply disp_univlaxmon_is_univalent_2.
    - apply disp_bicat_univstrongfunctor_is_univalent_2.
  Qed.

  Definition bicat_univstrongfunctor : bicat := total_bicat disp_univstrongfunctor.

  Definition bicat_univstrongfunctor_is_univalent_2 : is_univalent_2 bicat_univstrongfunctor.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univstrongfunctor_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

  (* We now show that the type of displayed objects and 1-cells is as we expect *)
  Definition strongfunctor_from_layer (C : bicat_of_univ_cats)
    : disp_univstrongfunctor C
      -> laxmon (C : univalent_category).
  Proof.
    intro M.
    use tpair.
    - apply laxmon_from_layer.
      use tpair.
      + apply (pr1 M).
      + apply (pr21 M).
    - use tpair.
      + apply (pr21 M).
      + apply (pr21 M).
  Defined.

  Definition strongfunctor_to_layer (C : bicat_of_univ_cats)
    : laxmon (C : univalent_category) -> disp_univstrongfunctor C.
  Proof.
    intro M.
    use tpair.
    - apply equivalence_laxmon_with_layer.
      split with (pr1 M).
      split with (pr12 M).
      apply (pr2 M).
    - exact tt.
  Defined.

  Definition equality_strongfunctor_with_layer (C : bicat_of_univ_cats) :
    laxmon (C : univalent_category) ≃ disp_univstrongfunctor C.
  Proof.
    use weq_iso.
    - apply strongfunctor_to_layer.
    - apply strongfunctor_from_layer.
    - intro ; apply idpath.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + apply isapropunit.

  Defined.

  Definition functor_strongfunctor_from_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongfunctor C)
             (tuuaD : disp_univstrongfunctor D)
    : (mor_disp (D := disp_univstrongfunctor) tuuaC tuuaD F) -> functor_strong_monoidal F
                           (strongfunctor_from_layer C tuuaC)
                           (strongfunctor_from_layer D tuuaD).
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_laxmon_with_layer.
      apply ptuua.
    - split.
      + apply (pr2 ptuua).
      + intro ; intro ; apply (pr2 ptuua).
  Defined.

  Definition functor_strongfunctor_to_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongfunctor C)
             (tuuaD : disp_univstrongfunctor D)
    : functor_strong_monoidal F
                           (strongfunctor_from_layer C tuuaC)
                           (strongfunctor_from_layer D tuuaD)
      -> mor_disp (D := disp_univstrongfunctor) tuuaC tuuaD F.
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_laxmon_with_layer.
      apply ptuua.
    - apply ptuua.
  Defined.

  Definition equality_functor_strongfunctor_with_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univstrongfunctor C)
             (tuuaD : disp_univstrongfunctor D)
    : functor_strong_monoidal F
                           (strongfunctor_from_layer C tuuaC)
                           (strongfunctor_from_layer D tuuaD)
      ≃ mor_disp (D := disp_univstrongfunctor) tuuaC tuuaD F.
  Proof.
    use weq_iso.
    - apply functor_strongfunctor_to_layer.
    - apply functor_strongfunctor_from_layer.
    - intro.
      use total2_paths_f ; apply idpath.
    - intro.
      use total2_paths_f.
      + use total2_paths_f.
        * apply idpath.
        * apply isapropunit.
      + use total2_paths_f.
        * apply isaprop_is_z_isomorphism.
        * repeat (apply funextsec ; intro) ; apply isaprop_is_z_isomorphism.
  Defined.

End StrongMonoidalFunctorLayer.
