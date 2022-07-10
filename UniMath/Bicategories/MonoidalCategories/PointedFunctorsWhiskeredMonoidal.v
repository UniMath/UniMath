(** **********************************************************

Ralph Matthes

2022
*)

(** **********************************************************

Contents :

- build monoidal category in whiskered form for the pointed endofunctors through a displayed monoidal category

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require UniMath.CategoryTheory.PointedFunctors.
Require UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.

Local Open Scope cat.

  Context (C : category).

  Definition pointedfunctors_disp_cat : disp_cat (cat_of_endofunctors C).
  Proof.
    use disp_struct.
    - intro F. exact (functor_identity C ⟹ pr1 F).
    - intros F G ptF ptG α. exact (∏ c : C, ptF c · pr1 α c = ptG c).
    - intros F G ptF ptG α. apply impred; intro c. apply C.
    - intros F ptF c. apply id_right.
    - abstract (intros F G H α β; cbn; intros ptF ptG ptH Hα Hβ c;
          rewrite assoc, Hα, Hβ;
                apply idpath ).
  Defined.

  Definition pointedfunctors_cat : category := total_category pointedfunctors_disp_cat.
  (** compare this with [UniMath.CategoryTheory.PointedFunctors.category_Ptd] *)

  Definition pointedfunctors_disp_tensor_data : disp_bifunctor_data (monoidal_of_endofunctors C)
    pointedfunctors_disp_cat pointedfunctors_disp_cat pointedfunctors_disp_cat.
  Proof.
    use tpair.
    - intros F G ptF ptG.
      exact (# (post_comp_functor (functor_identity C)) ptF · # (pre_comp_functor F) ptG).
      (** compare this with [UniMath.CategoryTheory.PointedFunctorsComposition.ptd_compose] *)
    - split.
      + intros F G1 G2 β ptF ptG1 ptG2 Hβ.
        cbn. intro c.
        rewrite <- Hβ.
        apply assoc'.
      + intros F1 F2 G α ptF1 ptF2 ptG Hα.
        cbn. intro c.
        rewrite <- Hα.
        do 2 rewrite <- assoc.
        apply maponpaths.
        etrans.
        { apply pathsinv0, (nat_trans_ax ptG). }
        apply idpath.
  Defined.

  Lemma pointedfunctors_disp_tensor_laws : is_disp_bifunctor pointedfunctors_disp_tensor_data.
  Proof.
    repeat split; red; intros; apply funextsec; intro; apply C.
  Qed.

  Definition pointedfunctors_disp_tensor : disp_tensor pointedfunctors_disp_cat (monoidal_of_endofunctors C) :=
    pointedfunctors_disp_tensor_data ,, pointedfunctors_disp_tensor_laws.

  Definition pointedfunctors_disp_unit : pointedfunctors_disp_cat I_{ monoidal_of_endofunctors C}
    := nat_trans_id (functor_identity C).

  Definition pointedfunctors_disp_moncat_data : disp_monoidal_data pointedfunctors_disp_cat
                                                  (monoidal_of_endofunctors C).
  Proof.
    exists pointedfunctors_disp_tensor. exists pointedfunctors_disp_unit.
    repeat split.
    - intros F ptF c. cbn. rewrite id_left; apply id_right.
    - intros F ptF c. cbn. rewrite id_left; apply id_right.
    - intros F ptF c. cbn. rewrite id_right; apply id_right.
      (* no goal left for inverse of right unitor *)
    - intros F G H ptF ptG ptH c. cbn. rewrite id_right. apply assoc'.
    - intros F G H ptF ptG ptH c. cbn. rewrite id_right. apply assoc.
  Defined.

  Lemma pointedfunctors_disp_moncat_laws : disp_monoidal_laws pointedfunctors_disp_moncat_data.
  Proof.
    repeat split; try red; try (intros; apply funextsec; intro; apply C).
  Qed.

  Definition pointedfunctors_disp_moncat : disp_monoidal pointedfunctors_disp_cat (monoidal_of_endofunctors C) :=
    pointedfunctors_disp_moncat_data ,, pointedfunctors_disp_moncat_laws.

  Definition pointedfunctors_moncat : monoidal pointedfunctors_cat := total_monoidal pointedfunctors_disp_moncat.
