(** * op2 bicategory. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.bicat.bicat.

Open Scope cat.

Section op2.

Variable C : prebicat.

Definition op2_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells.
Proof.
  exists C.
  intros a b f g. exact (g ==> f).
Defined.

Definition op2_prebicat_data : prebicat_data.
Proof.
  exists op2_prebicat_1_id_comp_cells.
  repeat (use tpair).
  - intros; apply id2.
  - intros; cbn. apply linvunitor.
  - intros; cbn. apply rinvunitor.
  - intros; cbn. apply lunitor.
  - intros; cbn. apply runitor.
  - intros; cbn. apply lassociator.
  - intros; cbn. apply rassociator.
  - intros; cbn. apply ( X0 • X ).
  - intros; cbn. apply ( f ◃ X ).
  - cbn; intros. apply (X ▹ g).
Defined.

Definition op2_prebicat_laws : prebicat_laws op2_prebicat_data.
Proof.
  repeat split; intros; cbn.
  - apply id2_right.
  - apply id2_left.
  - apply (!vassocr _ _ _ ).
  - apply lwhisker_id2.
  - apply id2_rwhisker.
  - apply lwhisker_vcomp.
  - apply rwhisker_vcomp.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - apply (!vcomp_whisker _ _  ).
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
  - admit.
  - admit.
Admitted.
End op2.
