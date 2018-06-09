(* *********************************************************************************** *)
(** * Bicategories

    Benedikt Ahrens, Marco Maggesi
    June 2018                                                                          *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** op1 bicategory.

    Bicategory obtained by formally reversing 1-arrows.                                *)
(* ----------------------------------------------------------------------------------- *)

Definition op1_2cell_struct (C : prebicat_1_id_comp_cells)
  : prebicat_2cell_struct (opp_precat_data C)
  := λ (a b : C) (f g : C ⟦ b, a ⟧), f ==> g.

Definition op1_prebicat_1_id_comp_cells (C : prebicat_1_id_comp_cells)
  : prebicat_1_id_comp_cells
  := (opp_precat_data C),, op1_2cell_struct C.

Definition op1_prebicat_data (C : prebicat_data)
  : prebicat_data.
Proof.
  exists (op1_prebicat_1_id_comp_cells C).
  red. cbn. unfold op1_2cell_struct.
  repeat use dirprodpair; intros until 0.
  - apply id2.
  - apply runitor.
  - apply lunitor.
  - apply rinvunitor.
  - apply linvunitor.
  - apply lassociator.
  - apply rassociator.
  - intros α β. exact ( α • β ).
  - intros α. exact (α ▹ f).
  - intros α. exact (g ◃ α).
Defined.

Definition op1_prebicat_laws (C : prebicat) : prebicat_laws (op1_prebicat_data C).
Proof.
  red. cbn. unfold op1_2cell_struct. cbn.
  repeat use tpair; cbn; intros until 0.
  - apply id2_left.
  - apply id2_right.
  - apply vassocr.
  - apply id2_rwhisker.
  - apply lwhisker_id2.
  - apply rwhisker_vcomp.
  - apply lwhisker_vcomp.
  - apply vcomp_runitor.
  - apply vcomp_lunitor.
  - apply rwhisker_rwhisker_alt.
  - apply pathsinv0, rwhisker_lwhisker_rassociator.
  - apply lwhisker_lwhisker_rassociator.
  - apply pathsinv0, vcomp_whisker.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
  - apply rassociator_lassociator.
  - apply lassociator_rassociator.
  - apply lunitor_lwhisker.
  - apply rassociator_rassociator.
Qed.

Definition op1_prebicat (C : prebicat) : prebicat
  := op1_prebicat_data C,, op1_prebicat_laws C.

Definition op1_isaset_cells (C : bicat) : isaset_cells (op1_prebicat C)
  := λ (a b : C) (f g : C ⟦ b, a ⟧), cellset_property f g.

Definition op1_bicat (C : bicat) : bicat
  := op1_prebicat C,, op1_isaset_cells C.
