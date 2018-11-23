(* *********************************************************************************** *)
(** * Bicategories

    Benedikt Ahrens, Marco Maggesi
    February 2018                                                                      *)
(* *********************************************************************************** *)

(* ----------------------------------------------------------------------------------- *)
(** ** op2 bicategory.

    Bicategory obtained by formally reversing 2-cells.                                 *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.

Open Scope cat.

Definition op2_2cell_struct (C : prebicat_1_id_comp_cells)
  : prebicat_2cell_struct C
  := λ (a b : C) (f g : C ⟦ a, b ⟧), g ==> f.

Definition op2_prebicat_1_id_comp_cells (C : prebicat_1_id_comp_cells)
  : prebicat_1_id_comp_cells
  := (C:precategory_data),, op2_2cell_struct C.

Definition op2_prebicat_data (C : prebicat_data)
  : prebicat_data.
Proof.
  exists (op2_prebicat_1_id_comp_cells C).
  repeat use dirprodpair.
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

Section op2.

Variable C : prebicat.

Definition op2_prebicat_laws : prebicat_laws (op2_prebicat_data C).
Proof.
  repeat split; intros; cbn.
  - apply id2_right.
  - apply id2_left.
  - apply (!vassocr _ _ _ ).
  - apply lwhisker_id2.
  - apply id2_rwhisker.
  - apply lwhisker_vcomp.
  - apply rwhisker_vcomp.
  - use lhs_left_invert_cell; [ apply is_invertible_2cell_linvunitor |].
    cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use lhs_right_invert_cell; [ apply is_invertible_2cell_linvunitor |].
    cbn.
    apply pathsinv0. apply vcomp_lunitor.
  - use lhs_left_invert_cell; [ apply is_invertible_2cell_rinvunitor |].
    cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use lhs_right_invert_cell; [ apply is_invertible_2cell_rinvunitor |].
    cbn.
    apply pathsinv0. apply vcomp_runitor.
  - apply lassociator_to_rassociator_pre.
    apply pathsinv0.
    etrans. apply (vassocr _ _ _ ).
    apply lassociator_to_rassociator_post.
    apply pathsinv0. apply lwhisker_lwhisker.
  - apply lassociator_to_rassociator_pre.
    apply pathsinv0.
    etrans. apply (vassocr _ _ _ ).
    apply lassociator_to_rassociator_post.
    apply pathsinv0. apply rwhisker_lwhisker.
  - apply pathsinv0, lassociator_to_rassociator_pre.
    apply pathsinv0.
    etrans. apply (vassocr _ _ _ ).
    apply lassociator_to_rassociator_post.
    apply rwhisker_rwhisker.
  - apply (!vcomp_whisker _ _  ).
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
  - use lhs_left_invert_cell.
    { use is_invertible_2cell_rwhisker.
      apply is_invertible_2cell_rinvunitor.
    } cbn.
    apply pathsinv0.
    use lhs_right_invert_cell.
    { use is_invertible_2cell_lwhisker.
      apply is_invertible_2cell_linvunitor.
    } cbn.
    apply pathsinv0.
    apply lassociator_to_rassociator_pre.
    apply pathsinv0, runitor_rwhisker.
  - use lhs_left_invert_cell.
    { use is_invertible_2cell_rwhisker.
      apply is_invertible_2cell_rassociator.
    } cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use lhs_right_invert_cell.
    { apply is_invertible_2cell_rassociator.
    } cbn.
    use lhs_right_invert_cell.
    { apply is_invertible_2cell_rassociator.
    } cbn.
    apply pathsinv0.
    repeat rewrite <- vassocr.
    use lhs_left_invert_cell.
    { apply is_invertible_2cell_rassociator.
    } cbn.
    use lhs_left_invert_cell.
    { apply is_invertible_2cell_lwhisker.
      apply is_invertible_2cell_rassociator.
    } cbn.
    apply pathsinv0.
    rewrite vassocr.
    apply lassociator_lassociator.
Qed.

Definition op2_prebicat : prebicat := op2_prebicat_data C ,, op2_prebicat_laws.

End op2.

Definition op2_isaset_cells (C : bicat) : isaset_cells (op2_prebicat C)
  := λ (a b : C) (f g : C ⟦ a, b ⟧), cellset_property g f.

Definition op2_bicat (C : bicat) : bicat
  := op2_prebicat C,, op2_isaset_cells C.
