(** *** Going into the opposite direction of [UniMath.Bicategories.Core.Examples.BicategoryFromWhiskeredMonoidal] *)
(** We fix a bicategory and an object of it and construct the (whiskered) monoidal category of endomorphisms.

Written by Ralph Matthes in 2019, adapted in 2022.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Unitors.

Local Open Scope cat.


Section Monoidal_Cat_From_Bicat.

Local Open Scope bicategory_scope.
Import Bicat.Notations.
Import MonoidalNotations.

Context {C : bicat}.
Context (c0: ob C).

Definition precategory_data_from_bicat_and_ob: precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (C⟦c0,c0⟧).
    + apply prebicat_cells.
  - intro c; apply id2.
  - intros a b c; apply vcomp2.
Defined.

Lemma is_precategory_data_from_prebicat_and_ob: is_precategory precategory_data_from_bicat_and_ob.
Proof.
  use make_is_precategory.
  - intros a b f; apply id2_left.
  - intros a b f; apply id2_right.
  - intros a b c d f g h; apply vassocr.
  - intros a b c d f g h; apply pathsinv0; apply vassocr.
Qed.

Definition precategory_from_bicat_and_ob: precategory := _,, is_precategory_data_from_prebicat_and_ob.

Lemma has_homsets_precategory_from_bicat_and_ob: has_homsets precategory_from_bicat_and_ob.
Proof.
  red. intros.
  apply (cellset_property(C:=C)).
Qed.

Definition category_from_bicat_and_ob: category := precategory_from_bicat_and_ob ,, has_homsets_precategory_from_bicat_and_ob.

Local Notation EndC := category_from_bicat_and_ob.

Definition tensor_from_bicat_and_ob: tensor category_from_bicat_and_ob.
Proof.
  use make_bifunctor.
  - use make_bifunctor_data.
    + intros a b. exact (a · b).
    + intros a b1 b2 β. exact (lwhisker _ β).
    + intros b a1 a2 α. exact (rwhisker _ α).
  - red; repeat split; red; cbn.
    + apply lwhisker_id2.
    + intros; apply id2_rwhisker.
    + intros; apply pathsinv0, lwhisker_vcomp.
    + intros; apply pathsinv0, rwhisker_vcomp.
    + intros; apply vcomp_whisker.
Defined.

Local Notation tensor := tensor_from_bicat_and_ob.

Definition monoidal_data_from_bicat_and_ob: monoidal_data category_from_bicat_and_ob.
Proof.
  use make_monoidal_data.
  - exact tensor.
  - exact (id₁ c0).
  - red; intros; apply lunitor.
  - red; intros; apply linvunitor.
  - red; intros; apply runitor.
  - red; intros; apply rinvunitor.
  - red; intros; apply rassociator.
  - red; intros; apply lassociator.
Defined.

Local Definition MD := monoidal_data_from_bicat_and_ob.

Local Definition leftunitor_law_from_bicat_and_ob: leftunitor_law lu_{MD} luinv_{MD}.
Proof.
  split; red; cbn.
  - apply vcomp_lunitor.
  - apply is_invertible_2cell_lunitor.
Defined.

Local Definition rightunitor_law_from_bicat_and_ob: rightunitor_law ru_{MD} ruinv_{MD}.
Proof.
  split; red; cbn.
  - apply vcomp_runitor.
  - apply is_invertible_2cell_runitor.
Defined.

Local Definition associator_law_from_bicat_and_ob: associator_law α_{MD} αinv_{MD}.
Proof.
  repeat split; try red; cbn.
  - apply lwhisker_lwhisker_rassociator.
  - intros; apply pathsinv0, rwhisker_rwhisker_alt.
  - apply rwhisker_lwhisker_rassociator.
  - apply is_invertible_2cell_rassociator.
  - apply is_invertible_2cell_rassociator.
Defined.

Local Lemma triangle_identity_from_bicat_and_ob: triangle_identity lu_{MD} ru_{MD} α_{MD}.
Proof.
  red; cbn. apply lunitor_lwhisker.
Qed.

(** the next two lemmas only for illustration that the extra triangle laws are already available in bicategories *)
Local Lemma triangle_identity'_from_bicat_and_ob: triangle_identity' lu_{MD} α_{MD}.
Proof.
  red; intros x y; cbn. rewrite <- lunitor_triangle. rewrite vassocr. rewrite rassociator_lassociator. apply id2_left.
Qed.

Local Lemma triangle_identity''_from_bicat_and_ob: triangle_identity'' ru_{MD} α_{MD}.
Proof.
  red; intros x y; cbn. apply runitor_triangle.
Qed.

Local Lemma pentagon_identity_from_bicat_and_ob: pentagon_identity α_{MD}.
Proof.
  red; cbn. apply rassociator_rassociator.
Qed.

Definition monoidal_from_bicat_and_ob: monoidal category_from_bicat_and_ob.
Proof.
  exists monoidal_data_from_bicat_and_ob.
  red.
  exists leftunitor_law_from_bicat_and_ob.
  exists rightunitor_law_from_bicat_and_ob.
  exists associator_law_from_bicat_and_ob.
  exists triangle_identity_from_bicat_and_ob.
  exact pentagon_identity_from_bicat_and_ob.
Defined.

End Monoidal_Cat_From_Bicat.
