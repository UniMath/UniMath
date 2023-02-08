(** an elementary construction of the monoidal category of endofunctors of a given category

    a general construction is available for bicategories and a fixed object therein

author: Ralph Matthes, 2023
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.

Local Open Scope cat.

Section FixACategory.

  Import MonoidalNotations.

  Context (C : category).

  Definition monendocat_tensor_data : bifunctor_data [C, C] [C, C] [C, C].
  Proof.
    use make_bifunctor_data.
    - intros a b. exact (functor_compose a b).
    - intros a b1 b2 β. exact (lwhisker_CAT _ β).
    - intros b a1 a2 α. exact (rwhisker_CAT _ α).
  Defined.

  (** we explicitly do not opacify the following definition: *)
  Definition monendocat_tensor_laws : is_bifunctor monendocat_tensor_data.
  Proof.
    red; repeat split; red; cbn.
    - apply lwhisker_id2_CAT.
    - intros; apply id2_rwhisker_CAT.
    - intros; apply pathsinv0, lwhisker_vcomp_CAT.
    - intros; apply pathsinv0, rwhisker_vcomp_CAT.
    - intros; apply vcomp_whisker_CAT.
  Defined.

  Definition monendocat_tensor : tensor [C, C] :=
    make_bifunctor monendocat_tensor_data monendocat_tensor_laws.

  Definition monendocat_monoidal_data : monoidal_data [C, C].
  Proof.
    use make_monoidal_data.
    - exact monendocat_tensor.
    - exact (id1_CAT C).
    - red; intros; apply lunitor_CAT.
    - red; intros; apply linvunitor_CAT.
    - red; intros; apply runitor_CAT.
    - red; intros; apply rinvunitor_CAT.
    - red; intros; apply rassociator_CAT.
    - red; intros; apply lassociator_CAT.
  Defined.

  Local Definition MD := monendocat_monoidal_data.

  Local Lemma monendocat_leftunitor_law: leftunitor_law lu_{MD} luinv_{MD}.
  Proof.
    split; red; cbn; intros.
    - apply vcomp_lunitor_CAT.
    - apply lunitor_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_rightunitor_law : rightunitor_law ru_{MD} ruinv_{MD}.
  Proof.
    split; red; cbn; intros.
    - apply vcomp_runitor_CAT.
    - apply runitor_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_associator_law : associator_law α_{MD} αinv_{MD}.
  Proof.
    repeat split; try red; cbn; intros.
    - apply lwhisker_lwhisker_rassociator_CAT.
    - intros; apply pathsinv0, rwhisker_rwhisker_alt_CAT.
    - apply rwhisker_lwhisker_rassociator_CAT.
    - apply lassociator_CAT_pointwise_is_z_iso.
    - apply lassociator_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_triangle_identity : triangle_identity lu_{MD} ru_{MD} α_{MD}.
  Proof.
    red; cbn. apply lunitor_lwhisker_CAT.
  Qed.

  Local Lemma monendocat_pentagon_identity : pentagon_identity α_{MD}.
  Proof.
    red; cbn; apply rassociator_rassociator_CAT.
  Qed.

  Definition monendocat_monoidal : monoidal [C, C].
  Proof.
    exists monendocat_monoidal_data.
    red.
    exists monendocat_leftunitor_law.
    exists monendocat_rightunitor_law.
    exists monendocat_associator_law.
    exists monendocat_triangle_identity.
    exact monendocat_pentagon_identity.
  Defined.

  End FixACategory.
