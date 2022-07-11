(*
This is the last file which concludes that the bicategory of univalent monoidal categories is again univalent.
In this file we conclude that both the bicategory of univalent monoidal categories with lax monoidal functors is univalent
and that the result still holds when we replace lax by strong monoidal functors.
*)

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Tensorlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Unitlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.TensorUnitlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.leftUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.rightUnitorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.associatorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.TensorUnitAssUnitorsLayer.

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
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import AssociatorUnitorsNotations.

Section LaxLayer.

  Definition bicat_univlaxmon_noprop : bicat := bicatcatsassunitors_total.

  Definition P_triangle : bicat_univlaxmon_noprop -> UU
    :=  λ C : bicat_univlaxmon_noprop,  ∏ (x y : assunitors_univcategory C),
        (ass^{C} x I_{C} y) · ((identity x) ⊗^{C} (lu^{C} y)) = (ru^{C} x) ⊗^{C} (identity y).

  Definition P_pentagon : bicat_univlaxmon_noprop -> UU
    := λ C : bicat_univlaxmon_noprop, ∏ (w x y z : assunitors_univcategory C),
        ((ass^{C} w x y) ⊗^{C} (identity z)) · (ass^{C} w (x⊗_{C} y) z) · ((identity w) ⊗^{C} (ass^{C} x y z))
        = (ass^{C} (w ⊗_{C} x) y z) · (ass^{C} w x (y ⊗_{C} z)).

  Definition P_triangle_pent : bicat_univlaxmon_noprop -> UU
    := λ C : bicat_univlaxmon_noprop, P_triangle C × P_pentagon C.

  Definition bicat_univlaxmon : bicat := fullsubbicat bicat_univlaxmon_noprop P_triangle_pent.

  Definition bicat_univlaxmon_is_univalent_2 : is_univalent_2 bicat_univlaxmon.
  Proof.
    apply is_univalent_2_fullsubbicat.
    - apply bicatcatsassunitors_is_univalent_2.
    - intro C.
      apply isapropdirprod.
      + repeat (apply impred_isaprop ; intro).
        apply homset_property.
      + repeat (apply impred_isaprop ; intro).
        apply homset_property.
  Qed.

  Definition bicat_univlaxmon_to_noprop : bicat_univlaxmon -> bicat_univlaxmon_noprop
    := λ C : bicat_univlaxmon, pr1 C.

End LaxLayer.

Module AssociatorUnitorsNotations.

  (* Notation "I_{ C }" := (assunitors_unit (bicat_univlaxmon_to_noprop C)).
  Notation "T_{ C }" := (assunitors_tensor (bicat_univlaxmon_to_noprop C)).
  Notation "x ⊗_{ C } y" := (tensor_on_ob T_{C} x y) (at level 31).
  Notation "f ⊗^{ C } g" := (tensor_on_hom T_{C} _ _ _ _ f g) (at level 31). *)

  Notation "lu^{ C }" := (assunitors_leftunitor (bicat_univlaxmon_to_noprop C)).
  Notation "ru^{ C }" := (assunitors_rightunitor (bicat_univlaxmon_to_noprop C)).
  Notation "ass^{ C }" := (assunitors_associator (bicat_univlaxmon_to_noprop C)).

End AssociatorUnitorsNotations.

Section StrongLayer.

  Import AssociatorUnitorsNotations.

  Definition P_sass : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,  ∏ (x y z :  assunitors_univcategory (bicat_univlaxmon_to_noprop C)),
        is_z_isomorphism (ass^{C} x y z).

  Definition P_slu : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,  ∏ (x :  assunitors_univcategory (bicat_univlaxmon_to_noprop C)),
        is_z_isomorphism (lu^{C} x).

  Definition P_sru : bicat_univlaxmon -> UU
    :=  λ C : bicat_univlaxmon,  ∏ (x :  assunitors_univcategory (bicat_univlaxmon_to_noprop C)),
        is_z_isomorphism (ru^{C} x).

  Definition P_strong : bicat_univlaxmon -> UU
    := λ C : bicat_univlaxmon, P_sass C × P_slu C × P_sru C.

  Definition bicat_univstrongmon : bicat := fullsubbicat bicat_univlaxmon P_strong.

  Definition bicat_is_univalent_2 : is_univalent_2 bicat_univstrongmon.
  Proof.
    apply is_univalent_2_fullsubbicat.
    - apply bicat_univlaxmon_is_univalent_2.
    - intro C.
      repeat (apply isapropdirprod).
      + repeat (apply impred_isaprop ; intro) ; apply isaprop_is_z_isomorphism.
      + repeat (apply impred_isaprop ; intro) ; apply isaprop_is_z_isomorphism.
      + repeat (apply impred_isaprop ; intro) ; apply isaprop_is_z_isomorphism.
  Qed.

End StrongLayer.
