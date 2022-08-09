(*
This is the last file which concludes that the bicategory of univalent monoidal categories is again univalent.
In this file we conclude that both the bicategory of univalent monoidal categories with lax monoidal functors is univalent
and that the result still holds when we replace lax by strong monoidal functors.
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

  Definition UMONCAT_strong : bicat := total_bicat disp_univstrongfunctor.

  Definition bicat_univstrongfunctor_is_univalent_2 : is_univalent_2 UMONCAT_strong.
  Proof.
    apply total_is_univalent_2.
    - apply disp_univstrongfunctor_is_univalent_2.
    - apply univalent_cat_is_univalent_2.
  Qed.

End StrongLayer.

Section EquivalenceWithCurried.

(* We now show that the type of displayed objects, 1-cells and 2-cells is as we expect *)
 (*  Definition tripent_from_layer (C : bicat_of_univ_cats)
    : disp_tripent C -> tensor_unit_unitors_associator_triangle_pentagon (C : univalent_category).
  Proof.
    intro M.
    use tpair.
    - apply assunitors_from_layer.
      apply M.
    - apply (pr2 M).
  Defined.

  Definition tripent_to_layer (C : bicat_of_univ_cats)
    : tensor_unit_unitors_associator_triangle_pentagon (C : univalent_category) → disp_tripent C.
  Proof.
    intro M.
    use tpair.
    - apply assunitors_to_layer.
      apply M.
    - apply (pr2 M).
  Defined.

  Definition equivalence_tripent_with_layer (C : bicat_of_univ_cats) :
    disp_tripent C ≃ tensor_unit_unitors_associator_triangle_pentagon (C : univalent_category).
  Proof.
    use weq_iso.
    - apply tripent_from_layer.
    - apply tripent_to_layer.
    - intro ; apply idpath.
    - intro ; apply idpath.
  Defined.

  Lemma equivalence_obtripent_oblayer
    : ob bicat_tripent ≃ ∑ C : bicat_of_univ_cats, tensor_unit_unitors_associator_triangle_pentagon (C : univalent_category).
  Proof.
    apply weqfibtototal.
    intro ; apply equivalence_tripent_with_layer.
  Defined.

  Definition functor_laxmon_from_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_tripent C)
             (tuuaD : disp_tripent D)
    : tuuaC -->[F] tuuaD
            -> functor_tensor_unit_unitors_associator F (assunitors_from_layer C (pr1 tuuaC)) (assunitors_from_layer D (pr1 tuuaD)).
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_assunitors_with_layer.
      apply (pr1 ptuua).
    - repeat split.
      + apply (pr121 ptuua).
      + apply (pr2 (pr121 ptuua)).
      + apply (pr221 ptuua).
  Defined.

  Definition functor_laxmon_to_layer
             {C D : bicat_of_univ_cats} {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_tripent C)
             (tuuaD : disp_tripent D)
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
             (tuuaC : disp_tripent C)
             (tuuaD : disp_tripent D)
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

  Import Notations.

  Definition nattrans_laxmon_from_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_tripent C} {tuuaD : disp_tripent D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : ptuuaF ==>[α] ptuuaG
      -> nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ ptuuaF)
          (functor_laxmon_from_layer _ _ ptuuaG)
          α.
  Proof.
    intro ntu.
    apply ntu.
    (* exists (λ x y, pr111 ntu x y).
    exact (pr211 ntu). *)
  Defined.

  Definition nattrans_laxmon_to_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_tripent C} {tuuaD : disp_tripent D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ ptuuaF)
          (functor_laxmon_from_layer _ _ ptuuaG)
          α
      -> ptuuaF ==>[α] ptuuaG.
  Proof.
    intro ntu.
    repeat (use tpair) ; try (exact tt) ; try (apply ntu).
  Defined.

  Definition equivalence_nattrans_laxmon_with_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_tripent C} {tuuaD : disp_tripent D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ ptuuaF)
          (functor_laxmon_from_layer _ _ ptuuaG)
          α
          ≃ ptuuaF ==>[α] ptuuaG.
  Proof.
    use weq_iso.
    - apply nattrans_laxmon_to_layer.
    - apply nattrans_laxmon_from_layer.
    - intro ; apply idpath.
    - intro.
      repeat (use total2_paths_f) ; try (apply idpath) ; try (apply isapropunit).
  Defined.

  Definition strongmon_from_layer (C : bicat_of_univ_cats)
    : disp_univstrongfunctor C -> strongmon (C : univalent_category).
  Proof.
    intro M.
    use tpair.
    - apply laxmon_from_layer.
      apply (pr1 M).
    - use tpair.
      + exact (pr211 M).
      + repeat (use tpair) ; apply (pr21 M).
  Defined.

  Definition strongmon_to_layer (C : bicat_of_univ_cats)
    : strongmon (C : univalent_category)  → disp_univstrongfunctor C.
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
  Defined.*)

End EquivalenceWithCurried.
