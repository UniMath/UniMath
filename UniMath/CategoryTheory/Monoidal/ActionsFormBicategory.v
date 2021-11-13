(** Constructs the bicategory of actions, strong action-based functors and their natural transformations

The construction goes through a displayed bicategory over the bicategoy of (small) categories.

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrongFunctorCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.


Import Bicat.Notations.

Local Open Scope cat.

Section FixAMonoidalCategory.

  Context (Mon_V : monoidal_cat).

Local Definition I : Mon_V := monoidal_cat_unit Mon_V.
Local Definition tensor : Mon_V ⊠ Mon_V ⟶ Mon_V := monoidal_cat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Local Definition α' : associator tensor := monoidal_cat_associator Mon_V.
Local Definition λ' : left_unitor tensor I := monoidal_cat_left_unitor Mon_V.
Local Definition ρ' : right_unitor tensor I := monoidal_cat_right_unitor Mon_V.

Let CAT := bicat_of_cats.

Definition actions_disp_cat_ob_mor : disp_cat_ob_mor CAT.
Proof.
  exists (fun A => action Mon_V A).
  intros A A' actn actn' F.
  exact (ob_disp (Strong_Functor_precategory_displayed Mon_V actn actn') F).
Defined.

Goal ∏ A A' actn actn' F, pr2 actions_disp_cat_ob_mor A A' actn actn' F =
                          actionbased_strength Mon_V actn actn' F.
Proof.
  intros.
  apply idpath.
Qed.

Definition actions_disp_cat_id_comp : disp_cat_id_comp CAT actions_disp_cat_ob_mor.
Proof.
  split.
  - intros A actn.
    apply ab_strength_identity_functor.
  - intros A1 A2 A3 F F' actn1 actn2 actn3 ζ ζ'.
    apply (ab_strength_composition Mon_V ζ ζ').
Defined.

Definition actions_disp_cat_data : disp_cat_data CAT :=
  actions_disp_cat_ob_mor ,, actions_disp_cat_id_comp.

Definition actions_disp_2cell_struct : disp_2cell_struct actions_disp_cat_data.
Proof.
  red.
  intros A A' F F' η actn actn' ζ ζ'.
  exact (mor_disp(D:=Strong_Functor_precategory_displayed Mon_V actn actn') ζ ζ' η).
Defined.

Goal ∏ A A' F F' η actn actn' ζ ζ', actions_disp_2cell_struct A A' F F' η actn actn' ζ ζ' =
        quantified_strong_functor_category_mor_diagram Mon_V actn actn' (F,, ζ) (F',, ζ') η.
Proof.
  intros.
  apply idpath.
Qed.

Definition actions_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells CAT :=
  actions_disp_cat_data ,, actions_disp_2cell_struct.

Lemma actions_disp_2cells_isaprop : disp_2cells_isaprop actions_disp_prebicat_1_id_comp_cells.
Proof.
  red.
  intros A A'. intros.
  apply impred; intros a; apply impred; intros v.
  apply (homset_property A').
Qed.

Lemma actions_disp_prebicat_ops : disp_prebicat_ops actions_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split.
  - intros A A' F actn actn' ζ a v.
    red. cbn.
    rewrite binprod_id. rewrite id_right.
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0, functor_id. }
    apply pathsinv0, id_left.
  - intros A A' F actn actn' ζ a v.
    red. cbn.
    rewrite id_right.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    rewrite id_left.
    rewrite functor_id.
    apply id_right.
  - intros A A' F actn actn' ζ a v.
    red. cbn.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    do 2 rewrite id_left.
    apply id_right.
  - intros A A' F actn actn' ζ a v.
    red. cbn.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    rewrite functor_id.
    rewrite id_left.
    apply idpath.
  - intros A A' F actn actn' ζ a v.
    red. cbn.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    do 2 rewrite id_left.
    apply id_right.
  - intros A1 A2 A3 A4 F1 F2 F3 actn1 actn2 actn3 actn4 ζ1 ζ2 ζ3 a v.
    red. cbn.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    rewrite id_right, id_left.
    rewrite <- assoc.
    apply maponpaths.
    apply functor_comp.
  - intros A1 A2 A3 A4 F1 F2 F3 actn1 actn2 actn3 actn4 ζ1 ζ2 ζ3 a v.
    red. cbn.
    rewrite binprod_id.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_id. }
    rewrite id_right, id_left.
    rewrite <- assoc.
    apply maponpaths.
    apply pathsinv0, functor_comp.
  - intros A A' F1 F2 F3 η η' actn actn' ζ1 ζ2 ζ3 Hypη Hypη' a v.
    red. cbn.
    rewrite <- (id_left (id v)).
    rewrite binprod_comp.
    etrans.
    2: { apply cancel_postcomposition, pathsinv0, functor_comp. }
    assert (Hypηinst := Hypη a v).
    assert (Hypη'inst := Hypη' a v).
    red in Hypηinst, Hypη'inst.
    etrans.
    { rewrite assoc. apply cancel_postcomposition. exact Hypηinst. }
    etrans.
    { rewrite <- assoc. apply maponpaths. exact Hypη'inst. }
    apply assoc.
  - intros A1 A2 A3 F G1 G2 η actn1 actn2 actn3 ζ ζ1 ζ2 Hypη a v.
    red. cbn.
    assert (Hypηinst := Hypη (pr1 F a) v).
    red in Hypηinst. unfold ActionBasedStrongFunctorCategory.ζ in Hypηinst. cbn in Hypηinst.
    etrans.
    2: { rewrite assoc. apply cancel_postcomposition.
         exact Hypηinst. }
    do 2 rewrite <- assoc.
    apply maponpaths.
    apply nat_trans_ax.
  - intros A1 A2 A3 F1 F2 G η actn1 actn2 actn3 ζ1 ζ2 ζ Hypη a v.
    red. cbn.
    assert (Hypηinst := Hypη a v).
    red in Hypηinst. unfold ActionBasedStrongFunctorCategory.ζ in Hypηinst. cbn in Hypηinst.
    etrans.
    { rewrite <- assoc. apply maponpaths. apply pathsinv0, functor_comp. }
    etrans.
    { do 2 apply maponpaths. exact Hypηinst. }
    clear Hypηinst.
    rewrite functor_comp.
    do 2 rewrite assoc.
    apply cancel_postcomposition.
    assert (ζnatinst := nat_trans_ax (pr1 ζ) (pr1 F1 a,, v) (pr1 F2 a,, v) (pr1 η a,, id₁ v)).
    apply pathsinv0, ζnatinst.
Qed.

Definition actions_disp_prebicat_data : disp_prebicat_data CAT :=
  actions_disp_prebicat_1_id_comp_cells ,, actions_disp_prebicat_ops.

(** the laws are all trivial since the 2-cells do not come with data on top of the natural transformations
    of the base bicategory [CAT] - this shows the benefits of the displayed approach *)
Lemma actions_disp_prebicat_laws : disp_prebicat_laws actions_disp_prebicat_data.
Proof.
  repeat split; red; intros; apply actions_disp_2cells_isaprop.
Qed.

Definition actions_disp_prebicat : disp_prebicat CAT :=
  actions_disp_prebicat_data ,, actions_disp_prebicat_laws.

Lemma actions_has_disp_cellset : has_disp_cellset actions_disp_prebicat.
Proof.
  red.
  intros A A'. intros.
  cbn.
  apply isasetaprop.
  apply actions_disp_2cells_isaprop.
Qed.

Definition actions_disp_bicat : disp_bicat CAT :=
  actions_disp_prebicat ,, actions_has_disp_cellset.

Definition actions_disp_locally_groupoid : disp_locally_groupoid actions_disp_bicat.
Proof.
  red.
  intros A A' F F' invertibleη actn actn' ζ ζ' Hypη.
  use tpair.
  - intros a v.
    red.
    assert (Hypηinst := Hypη a v).
    red in Hypηinst.
    apply pathsinv0.
    set (η_z_nat_iso := z_nat_iso_from_z_iso (homset_property A') invertibleη).
    set (η_z_nat_iso_inst1 := nat_z_iso_pointwise_z_iso η_z_nat_iso (ActionBasedStrongFunctorCategory.odot Mon_V actn (a, v))).
    apply (z_iso_inv_on_left _ _ _ _ η_z_nat_iso_inst1).
    rewrite <- assoc.
    set (η_z_nat_iso_inst2 := nat_z_iso_pointwise_z_iso η_z_nat_iso a).
    set (aux1_z_iso := precatbinprod_z_iso η_z_nat_iso_inst2 (identity_z_iso v)).
    set (aux2_z_iso := functor_on_z_iso (ActionBasedStrongFunctorCategory.odot' Mon_V actn') aux1_z_iso).
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ aux2_z_iso).
    exact Hypηinst.
  - split; apply actions_disp_2cells_isaprop.
Defined.

Definition actions_bicat : bicat := total_bicat actions_disp_bicat.

End FixAMonoidalCategory.
