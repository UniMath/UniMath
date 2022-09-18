(*
This is the last file which concludes that the bicategory of univalent monoidal categories is again univalent.
In this file we conclude that both the bicategory of univalent monoidal categories with lax monoidal functors, denoted by UMONCAT, is univalent
and that the result still holds when we replace lax by strong monoidal functors, we denote this bicategory by UMONCAT_strong.
*)

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.
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

Import Bicat.Notations.

Import AssociatorUnitorsNotations.

Local Definition bicat_univlaxmon_noprop : bicat := total_bicat disp_tensor_unit_unitors_associator.

Section MonoidalCategoryLayer.

  Definition P_triangle_pentagon : bicat_univlaxmon_noprop -> UU
    :=  λ C,
        triangle_pentagon (pr2 (assunitors_from_layer (uc (pr1 C,, pr12 C))  (pr2 C))).

  Definition P_assinv : bicat_univlaxmon_noprop -> UU
    :=  λ C,
        associator_invertible (pr2 (assunitors_from_layer (pr1 C)  (pr2 C))).

   Definition P_luinv : bicat_univlaxmon_noprop -> UU
    :=  λ C,
        lunitor_invertible (pr2 (assunitors_from_layer (pr1 C)  (pr2 C))).
    Definition P_ruinv : bicat_univlaxmon_noprop -> UU
    :=  λ C,
        runitor_invertible (pr2 (assunitors_from_layer (pr1 C)  (pr2 C))).

  Definition P_inv : bicat_univlaxmon_noprop -> UU
    := λ C, P_assinv C × P_luinv C × P_ruinv C.

  Definition P_prop : bicat_univlaxmon_noprop -> UU
    := λ C, P_triangle_pentagon C × P_inv C.

  Lemma isaprop_P_prop (C : bicat_univlaxmon_noprop) : isaprop (P_prop C).
  Proof.
    repeat (apply isapropdirprod).
    - apply isaprop_triangle.
    - apply isaprop_pentagon.
    - apply isaprop_associator_invertible.
    - apply isaprop_lunitor_invertible.
    - apply isaprop_runitor_invertible.
  Qed.

  Definition disp_bicat_univmon : disp_bicat bicat_univlaxmon_noprop
    := disp_fullsubbicat bicat_univlaxmon_noprop P_prop.

  Lemma disp_bicat_tripent_is_univalent_2 : disp_univalent_2 disp_bicat_univmon.
  Proof.
    split.
    - apply disp_univalent_2_0_fullsubbicat.
      + apply bidisp_assunitors_is_univalent_2.
      + intro ; apply isaprop_P_prop.
    - apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Definition disp_univmon : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ disp_bicat_univmon.

  Definition disp_univmon_is_univalent_2
    : disp_univalent_2 disp_univmon.
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
    - apply disp_bicat_tripent_is_univalent_2.
  Qed.

  Lemma disp_univmon_disp_2cells_isaprop :  disp_2cells_isaprop disp_univmon.
  Proof.
    apply disp_2cells_isaprop_sigma.
    + apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    + apply disp_2cells_isaprop_fullsubbicat.
  Qed.

  Lemma disp_univmon_disp_locally_groupoid :  disp_locally_groupoid disp_univmon.
  Proof.
    apply disp_locally_groupoid_sigma.
    - apply univalent_cat_is_univalent_2.
    - apply disp_tensor_unit_unitors_associator_disp_2cells_isaprop.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_tensor_unit_unitors_associator_disp_locally_groupoid.
    - apply disp_locally_groupoid_fullsubbicat.
  Qed.

  (* UMONCAT is the bicategory defined as follows:
     - Objects: Monoidal categories (over univalent categories).
     - Morphisms: Lax monoidal functors.
     - 2-cells: Monoidal natural transformations.

     This bicategory is constructed precisely such that
     we are able to carry out a modular proof of univalence,
     as seen in UMONCAT_is_univalent_2.
   *)
  Definition UMONCAT : bicat := total_bicat disp_univmon.

  Definition UMONCAT_is_univalent_2 : is_univalent_2 UMONCAT.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univmon_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

  Definition UMONCAT_category (C : UMONCAT) : univalent_category := pr1 C.

  Definition UMONCAT_tensorunit (C : UMONCAT) : tensor_unit (UMONCAT_category C)
    := (pr112 C).
  Definition UMONCAT_tensor (C : UMONCAT) : tensor (UMONCAT_category C)
    := pr1 (UMONCAT_tensorunit C).
  Definition UMONCAT_unit (C : UMONCAT) : UMONCAT_category C
    := pr2 (UMONCAT_tensorunit C).

  Definition UMONCAT_lunitor (C : UMONCAT) : CurriedMonoidalCategories.lunitor (UMONCAT_tensorunit C)
    := pr11 (pr212 C).
  Definition UMONCAT_runitor (C : UMONCAT) : CurriedMonoidalCategories.runitor (UMONCAT_tensorunit C)
    := (pr21 (pr212 C)).
  Definition UMONCAT_associator (C : UMONCAT) : CurriedMonoidalCategories.associator (UMONCAT_tensorunit C)
    := (pr2 (pr212 C)).
  Definition UMONCAT_unitorsassociator (C : UMONCAT)
    : unitors_associator (UMONCAT_tensorunit C)
    := UMONCAT_lunitor C ,, UMONCAT_runitor C ,, UMONCAT_associator C.

  Definition UMONCAT_functor {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : functor (UMONCAT_category C) (UMONCAT_category D)
    := pr1 F.

  Definition UMONCAT_functortensorunit {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : functor_tensor_unit (UMONCAT_tensorunit C) (UMONCAT_tensorunit D) (UMONCAT_functor F)
    := (pr112 F).

  Definition UMONCAT_functortensor {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : preserves_tensor (UMONCAT_tensor C) (UMONCAT_tensor D) (UMONCAT_functor F)
    := pr1 (UMONCAT_functortensorunit F).

  Definition UMONCAT_functorunit {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : preserves_unit (UMONCAT_unit C) (UMONCAT_unit D) (UMONCAT_functor F)
    := pr2 (UMONCAT_functortensorunit F).

  Definition UMONCAT_functorlunitor {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : preserves_lunitor (UMONCAT_functortensorunit F) (UMONCAT_lunitor C) (UMONCAT_lunitor D)
    :=  pr11 (pr212 F).
  Definition UMONCAT_functorrunitor {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : preserves_runitor (UMONCAT_functortensorunit F) (UMONCAT_runitor C) (UMONCAT_runitor D)
    := pr21 (pr212 F).
  Definition UMONCAT_functorassociator {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : preserves_associator (UMONCAT_functortensorunit F) (UMONCAT_associator C) (UMONCAT_associator D)
    := pr2 (pr212 F).

  Definition UMONCAT_functorunitorsassociator {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : functor_unitors_associator (UMONCAT_unitorsassociator C) (UMONCAT_unitorsassociator D) (UMONCAT_functortensorunit F)
    := UMONCAT_functorlunitor F ,, UMONCAT_functorrunitor F ,, UMONCAT_functorassociator F.

End MonoidalCategoryLayer.

Module UMONCAT_Notations.

  Notation "cat( C )" := (UMONCAT_category C).
  Notation "tensor( C )" := (UMONCAT_tensor C).
  Notation "unit( C )" := (UMONCAT_unit C).
  Notation "lunitor( C )" := (UMONCAT_lunitor C).
  Notation "runitor( C )" := (UMONCAT_runitor C).
  Notation "associator( C )" := (UMONCAT_associator C).

  Notation "functor( F )" := (UMONCAT_functor F).
  Notation "functortensorunit( F )" := (UMONCAT_functortensorunit F).
  Notation "functortensor( F )" := (UMONCAT_functortensor F).
  Notation "functorunit( F )" := (UMONCAT_functorunit F).
  Notation "functorunitorsassociator( F )" := (UMONCAT_functorunitorsassociator F).
  Notation "functorlunitor( F )" := (UMONCAT_functorlunitor F).
  Notation "functorrunitor( F )" := (UMONCAT_functorrunitor F).
  Notation "functorassociator( F )" := (UMONCAT_functorassociator F).

End UMONCAT_Notations.

Section StrongLayer.

  Import UMONCAT_Notations.
  Import Bicat.Notations.

  Definition P_strong_preserving : ∏ (C D : UMONCAT), UMONCAT⟦C,D⟧ -> UU
    := λ _ _ F, functor_strong functorunitorsassociator(F).

  Lemma isaprop_P_strong_preserving {C D : UMONCAT} (F : UMONCAT⟦C,D⟧)
    : isaprop (P_strong_preserving C D F).
  Proof.
    apply isapropdirprod.
    - apply isaprop_is_z_isomorphism.
    - repeat (apply impred_isaprop ; intro).
      apply isaprop_is_z_isomorphism.
  Qed.

  Definition Pid_strong_preserving :
    ∏ (C : UMONCAT), P_strong_preserving _ _ (id₁ C).
  Proof.
    intro C.
    use tpair.
    - apply identity_is_z_iso.
    - intro ; intro.
      apply identity_is_z_iso.
  Defined.

  Definition Pcomp_strong_preserving :
    ∏ (C D E : UMONCAT) (F : UMONCAT⟦C,D⟧) (G : UMONCAT⟦D,E⟧),
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

  Definition disp_bicat_univstrongfunctor : disp_bicat UMONCAT
    := disp_sub1cell_bicat UMONCAT P_strong_preserving Pid_strong_preserving Pcomp_strong_preserving.

  Definition disp_bicat_univstrongfunctor_is_univalent_2 : disp_univalent_2 disp_bicat_univstrongfunctor.
  Proof.
    apply disp_sub1cell_univalent_2.
    - apply UMONCAT_is_univalent_2.
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
    apply sigma_disp_univalent_2_with_props ; try (apply disp_univmon_is_univalent_2).
    - apply univalent_cat_is_univalent_2.
    - apply disp_univmon_disp_2cells_isaprop.
    - apply disp_univstrongfunctor_disp_2cells_isaprop.
    - apply disp_sub1cell_univalent_2.
      + apply UMONCAT_is_univalent_2.
      + intro ; intros ; apply isaprop_P_strong_preserving.
    - apply disp_univmon_disp_locally_groupoid.
    - apply disp_univstrongfunctor_disp_locally_groupoid.
    - apply disp_bicat_univstrongfunctor_is_univalent_2.
  Qed.

  (* UMONCAT_strong is the bicategory defined as follows:
     - Objects: Monoidal categories (over univalent categories).
     - Morphisms: Strong monoidal functors (not requiring any functorial strength).
     - 2-cells: Monoidal natural transformations.

     This bicategory is constructed precisely such that
     we are able to carry out a modular proof of univalence,
     as seen in UMONCAT_strong_is_univalent_2.
   *)
  Definition UMONCAT_strong : bicat := total_bicat disp_univstrongfunctor.

  Definition UMONCAT_strong_is_univalent_2 : is_univalent_2 UMONCAT_strong.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univstrongfunctor_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

End StrongLayer.
