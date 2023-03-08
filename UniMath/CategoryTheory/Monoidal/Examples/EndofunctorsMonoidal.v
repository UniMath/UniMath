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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.

Import MonoidalNotations.

Local Open Scope cat.

Section FixACategory.

  Context (C : category).

  Definition monendocat_tensor_data : bifunctor_data [C, C] [C, C] [C, C].
  Proof.
    use make_bifunctor_data.
    - intros a b. exact (functor_compose a b).
    - intros a b1 b2 β. exact (lwhisker_CAT _ β).
    - intros b a1 a2 α. exact (rwhisker_CAT _ α).
  Defined.

  (* (** we explicitly do not opacify the following definition: *) *)
  Definition monendocat_tensor_laws : is_bifunctor monendocat_tensor_data.
  Proof.
    split5.
    - intro; apply lwhisker_id2_CAT.
    - intro; intros; apply id2_rwhisker_CAT.
    - intro; intros; apply pathsinv0, lwhisker_vcomp_CAT.
    - intro; intros; apply pathsinv0, rwhisker_vcomp_CAT.
    - intro; intros; apply vcomp_whisker_CAT.
  Qed. (* Defined. *)

  Definition monendocat_tensor : bifunctor [C, C] [C, C] [C, C] :=
    make_bifunctor monendocat_tensor_data monendocat_tensor_laws.

  Definition monendocat_monoidal_data : monoidal_data [C, C].
  Proof.
    use make_monoidal_data.
    - exact monendocat_tensor_data.
    - exact (id1_CAT C).
    - intro; apply lunitor_CAT.
    - intro; apply linvunitor_CAT.
    - intro; apply runitor_CAT.
    - intro; apply rinvunitor_CAT.
    - intro; apply rassociator_CAT.
    - intro; apply lassociator_CAT.
  Defined.

  Local Definition MD := monendocat_monoidal_data.

  Local Lemma monendocat_leftunitor_law: leftunitor_law lu_{MD} luinv_{MD}.
  Proof.
    split.
    - intro; intros; apply vcomp_lunitor_CAT.
    - intro; apply lunitor_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_rightunitor_law : rightunitor_law ru_{MD} ruinv_{MD}.
  Proof.
    split.
    - intro; intros; apply vcomp_runitor_CAT.
    - intro; apply runitor_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_associator_law : associator_law α_{MD} αinv_{MD}.
  Proof.
    split4.
    - intro; intros; apply lwhisker_lwhisker_rassociator_CAT.
    - intro; intros; apply pathsinv0, rwhisker_rwhisker_alt_CAT.
    - intro; intros; apply rwhisker_lwhisker_rassociator_CAT.
    - split.
      + apply (pr22 (lassociator_CAT_pointwise_is_z_iso _ _ _)).
      + apply lassociator_CAT_pointwise_is_z_iso.
  Qed.

  Local Lemma monendocat_triangle_identity : triangle_identity lu_{MD} ru_{MD} α_{MD}.
  Proof.
    intro; intros. apply lunitor_lwhisker_CAT.
  Qed.

  Local Lemma monendocat_pentagon_identity : pentagon_identity α_{MD}.
  Proof.
    intro; intros. apply rassociator_rassociator_CAT.
  Qed.

  Definition monendocat_monoidal : monoidal [C, C].
  Proof.
    exists monendocat_monoidal_data.
    exists monendocat_tensor_laws.
    exists monendocat_leftunitor_law.
    exists monendocat_rightunitor_law.
    exists monendocat_associator_law.
    exists monendocat_triangle_identity.
    exact monendocat_pentagon_identity.
  Defined.
End FixACategory.
