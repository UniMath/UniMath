(** the coslice category I/V for a monoidal category is again monoidal

The coslice objects have a morphism from the monoidal unit I to an object of V. Since I is often not a terminal object 1 of V,
one cannot speak of pointed objects here; I suggest to call them monoidal-pointed objects.

author: Ralph Matthes 2022
 *)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.coslicecat.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section A.

Context {V : category} (Mon_V : monoidal V).

Let cosliced : disp_cat V := coslice_cat_disp V I_{ Mon_V}.

Definition monoidal_pointed_objects_disp_tensor_data : disp_bifunctor_data Mon_V cosliced cosliced cosliced.
Proof.
  use make_disp_bifunctor_data.
  - intros v w pv pw. exact (luinv^{Mon_V}_{I_{ Mon_V}} · pv ⊗^{Mon_V} pw).
  - intros v w w' g pv pw pw' Hypg. cbn in Hypg. cbn.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- Hypg.
    unfold functoronmorphisms1.
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0, bifunctor_leftcomp.
  - intros v v' w f pv pv' pw Hypf. cbn.
    rewrite assoc'.
    apply maponpaths.
    rewrite <- Hypf.
    do 2 rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    rewrite assoc'.
    apply maponpaths.
     apply pathsinv0, bifunctor_rightcomp.
Defined.

Lemma monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor : is_disp_bifunctor monoidal_pointed_objects_disp_tensor_data.
Proof.
  repeat split; red; intros; apply V.
Qed.

Definition monoidal_pointed_objects_disp_tensor : disp_tensor cosliced Mon_V
  := monoidal_pointed_objects_disp_tensor_data,,monoidal_pointed_objects_disp_tensor_data_is_disp_bifunctor.

Lemma monoidal_pointed_objects_disp_data_verif :
  disp_leftunitor_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_leftunitorinv_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_rightunitor_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_rightunitorinv_data monoidal_pointed_objects_disp_tensor (identity I_{ Mon_V})
    × disp_associator_data monoidal_pointed_objects_disp_tensor
    × disp_associatorinv_data monoidal_pointed_objects_disp_tensor.
Proof.
  repeat split; red.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_rightid.
    rewrite id_left.
    rewrite assoc'.
    rewrite monoidal_leftunitornat.
    rewrite assoc.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v pv. cbn.
    rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    rewrite bifunctor_rightid.
    rewrite id_right.
    rewrite monoidal_leftunitorinvnat.
    apply idpath.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    rewrite assoc'.
    rewrite monoidal_rightunitornat.
    rewrite assoc.
    rewrite <- unitors_coincide_on_unit.
    rewrite (pr2 (monoidal_leftunitorisolaw Mon_V _)).
    apply id_left.
  - intros v pv. cbn.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    rewrite <- monoidal_rightunitorinvnat.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply unitorsinv_coincide_on_unit.
  - intros v w u pv pw pu. cbn.
    rewrite assoc'.
    apply maponpaths.
    unfold functoronmorphisms1.
    repeat rewrite bifunctor_rightcomp.
    repeat rewrite bifunctor_leftcomp.
    repeat rewrite assoc'.
    rewrite <- monoidal_associatornatleft.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat rewrite assoc'.
    rewrite <- monoidal_associatornatleftright.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply (z_iso_inv_to_right _ _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, monoidal_triangle_identity_inv. }
    repeat rewrite <- bifunctor_rightcomp.
    apply maponpaths.
    rewrite unitorsinv_coincide_on_unit.
    apply monoidal_rightunitorinvnat.
  - intros v w u pv pw pu. cbn.
    rewrite assoc'.
    apply maponpaths.
    repeat rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    repeat rewrite bifunctor_rightcomp.
    repeat rewrite bifunctor_leftcomp.
    repeat rewrite assoc'.
    rewrite monoidal_associatorinvnatright.
    admit.

    (* 1 goal to solve *)



Admitted.

Definition monoidal_pointed_objects_disp_data : disp_monoidal_data cosliced Mon_V.
Proof.
  exists monoidal_pointed_objects_disp_tensor.
  use tpair.
  - apply identity.
  - exact monoidal_pointed_objects_disp_data_verif.
Defined.

Lemma monoidal_pointed_objects_disp_laws : disp_monoidal_laws monoidal_pointed_objects_disp_data.
Proof.
  red; repeat split; try red; intros; apply V.
Qed.

Definition monoidal_pointed_objects_disp : disp_monoidal cosliced Mon_V
  := monoidal_pointed_objects_disp_data,,monoidal_pointed_objects_disp_laws.

Definition monoidal_pointed_objects : monoidal (coslice_cat_total V I_{Mon_V})
  := total_monoidal monoidal_pointed_objects_disp.

End A.
