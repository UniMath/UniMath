(* ----------------------------------------------------------------------------------- *)
(** ** op2 bicategory.

    Bicategory obtained by formally reversing 2-cells.

    Benedikt Ahrens, Marco Maggesi
    February 2018                                                                      *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.

Local Open Scope cat.

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
  repeat use make_dirprod.
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

Definition op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op2_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α → @is_invertible_2cell C X Y g f α.
Proof.
  intros Hα.
  use tpair.
  - apply Hα.
  - split ; apply Hα.
Defined.

Definition bicat_is_invertible_2cell_to_op2_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op2_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : @is_invertible_2cell C X Y g f α → is_invertible_2cell α.
Proof.
  intros Hα.
  use tpair.
  - apply Hα.
  - split ; apply Hα.
Defined.

Definition op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op2_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : @is_invertible_2cell C X Y g f α ≃ is_invertible_2cell α.
Proof.
  use weqimplimpl.
  - exact (bicat_is_invertible_2cell_to_op2_bicat_is_invertible_2cell α).
  - exact (op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell α).
  - apply isaprop_is_invertible_2cell.
  - apply isaprop_is_invertible_2cell.
Defined.

Definition bicat_invertible_2cell_is_op2_bicat_invertible_2cell
           {C : bicat}
           {X Y : op2_bicat C}
           (f g : X --> Y)
  : @invertible_2cell C X Y g f ≃ invertible_2cell f g.
Proof.
  use weqfibtototal.
  intro α.
  apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
Defined.

Definition op2_bicat_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op2_bicat C}
           (f : X --> Y)
  : left_adjoint_equivalence f → @left_adjoint_equivalence C X Y f.
Proof.
  intros Hf.
  use tpair.
  - use tpair.
    + exact (left_adjoint_right_adjoint Hf).
    + split.
      * exact ((left_equivalence_unit_iso Hf)^-1).
      * exact ((left_equivalence_counit_iso Hf)^-1).
  - split ; split.
    + use inv_cell_eq ; cbn.
      * is_iso.
        ** apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
        ** apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
      * is_iso.
      * exact (internal_triangle1 Hf).
    + use inv_cell_eq ; cbn.
      * is_iso.
        ** apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
        ** apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
      * is_iso.
      * exact (internal_triangle2 Hf).
    + cbn.
      apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
      is_iso.
    + cbn.
      apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
      is_iso.
Defined.

Definition bicat_left_adjoint_equivalence_to_op2_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op2_bicat C}
           (f : X --> Y)
  : @left_adjoint_equivalence C X Y f → left_adjoint_equivalence f.
Proof.
  intros Hf.
  use tpair.
  - use tpair.
    + exact (left_adjoint_right_adjoint Hf).
    + split.
      * exact ((left_equivalence_unit_iso Hf)^-1).
      * exact ((left_equivalence_counit_iso Hf)^-1).
  - split ; split.
    + use inv_cell_eq ; cbn.
      * apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
        is_iso.
      * apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
        is_iso.
      * exact (internal_triangle1 Hf).
    + use inv_cell_eq ; cbn.
      * apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
        is_iso.
      * apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
        is_iso.
      * exact (internal_triangle2 Hf).
    + cbn.
      apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
      is_iso.
    + cbn.
      apply op2_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
      is_iso.
Defined.

Definition op2_bicat_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op2_bicat C}
           (f : X --> Y)
  : @left_adjoint_equivalence C X Y f ≃ left_adjoint_equivalence f.
Proof.
  use make_weq.
  - exact (bicat_left_adjoint_equivalence_to_op2_bicat_left_adjoint_equivalence f).
  - use isweq_iso.
    + exact (op2_bicat_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence f).
    + intros x.
      use subtypePath.
      * intro.
        do 2 apply isapropdirprod ; try (apply C) ; apply isaprop_is_invertible_2cell.
      * reflexivity.
    + intros x.
      use subtypePath.
      * intro.
        do 2 apply isapropdirprod ; try (apply C) ; apply isaprop_is_invertible_2cell.
      * reflexivity.
Defined.

Definition bicat_adjoint_equivalence_is_op2_bicat_adjoint_equivalence
           {C : bicat}
           (X Y : op2_bicat C)
  : @adjoint_equivalence C X Y ≃ adjoint_equivalence X Y.
Proof.
  use weqfibtototal.
  intro α.
  apply op2_bicat_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence.
Defined.
