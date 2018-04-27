(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(** * op2 bicategory. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

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
  - use inv_cell_to_cell_post; [ apply is_equivalence_linvunitor |].
    cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use cell_to_inv_cell_post; [ apply is_equivalence_linvunitor |].
    cbn.
    apply pathsinv0. apply vcomp_lunitor.
  - use inv_cell_to_cell_post; [ apply is_equivalence_rinvunitor |].
    cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use cell_to_inv_cell_post; [ apply is_equivalence_rinvunitor |].
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
  - use inv_cell_to_cell_post.
    { use is_equivalence_rwhisker.
      apply is_equivalence_rinvunitor.
    } cbn.
    apply pathsinv0.
    use cell_to_inv_cell_post.
    { use is_equivalence_lwhisker.
      apply is_equivalence_linvunitor.
    } cbn.
    apply pathsinv0.
    apply lassociator_to_rassociator_pre.
    apply pathsinv0, runitor_rwhisker.
  - use inv_cell_to_cell_post.
    { use is_equivalence_rwhisker.
      apply is_equivalence_rassociator.
    } cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    use cell_to_inv_cell_post.
    { apply is_equivalence_rassociator.
    } cbn.
    use cell_to_inv_cell_post.
    { apply is_equivalence_rassociator.
    } cbn.
    apply pathsinv0.
    repeat rewrite <- vassocr.
    use inv_cell_to_cell_post.
    { apply is_equivalence_rassociator.
    } cbn.
    use inv_cell_to_cell_post.
    { apply is_equivalence_lwhisker.
      apply is_equivalence_rassociator.
    } cbn.
    apply pathsinv0.
    rewrite vassocr.
    apply lassociator_lassociator.
Qed.

Definition op2_prebicat : prebicat := _ ,, op2_prebicat_laws.

End op2.
