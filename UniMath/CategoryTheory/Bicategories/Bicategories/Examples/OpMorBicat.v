(* *********************************************************************************** *)
(** op1 bicategory.

    Bicategory obtained by formally reversing 1-arrows.

    Benedikt Ahrens, Marco Maggesi
    June 2018                                                                          *)
(* *********************************************************************************** *)

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
  repeat use make_dirprod; intros *.
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
  repeat use tpair; cbn; intros *.
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

Definition op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op1_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α → @is_invertible_2cell C Y X f g α.
Proof.
  intros Hα.
  use tpair.
  - apply Hα.
  - split ; apply Hα.
Defined.

Definition bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op1_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : @is_invertible_2cell C Y X f g α → is_invertible_2cell α.
Proof.
  intros Hα.
  use tpair.
  - apply Hα.
  - split ; apply Hα.
Defined.

Definition op1_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell
           {C : bicat}
           {X Y : op1_bicat C}
           {f g : X --> Y}
           (α : f ==> g)
  : @is_invertible_2cell C Y X f g α ≃ is_invertible_2cell α.
Proof.
  use weqimplimpl.
  - exact (bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell α).
  - exact (op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell α).
  - apply isaprop_is_invertible_2cell.
  - apply isaprop_is_invertible_2cell.
Defined.

Definition bicat_invertible_2cell_is_op1_bicat_invertible_2cell
           {C : bicat}
           {X Y : op1_bicat C}
           (f g : X --> Y)
  : @invertible_2cell C Y X f g ≃ invertible_2cell f g.
Proof.
  use weqfibtototal.
  intro α.
  apply op1_bicat_is_invertible_2cell_is_bicat_is_invertible_2cell.
Defined.

Definition op1_bicat_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op1_bicat C}
           (f : X --> Y)
  : left_adjoint_equivalence f → @left_adjoint_equivalence C Y X f.
Proof.
  intros Hf.
  use tpair.
  - use tpair.
    + exact (left_adjoint_right_adjoint Hf).
    + split.
      * exact ((left_equivalence_counit_iso Hf)^-1).
      * exact ((left_equivalence_unit_iso Hf)^-1).
  - split ; split.
    + use inv_cell_eq ; cbn.
      * is_iso.
        ** apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
        ** apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
      * is_iso.
      * cbn.
        rewrite !vassocr.
        exact (internal_triangle1 Hf).
    + use inv_cell_eq ; cbn.
      * is_iso.
        ** apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
        ** apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
           is_iso.
      * is_iso.
      * cbn.
        rewrite !vassocr.
        exact (internal_triangle2 Hf).
    + cbn.
      apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
      is_iso.
    + cbn.
      apply op1_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell.
      is_iso.
Defined.

Definition bicat_left_adjoint_equivalence_to_op1_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op1_bicat C}
           (f : X --> Y)
  : @left_adjoint_equivalence C Y X f → left_adjoint_equivalence f.
Proof.
  intros Hf.
  use tpair.
  - use tpair.
    + exact (left_adjoint_right_adjoint Hf).
    + split.
      * exact ((left_equivalence_counit_iso Hf)^-1).
      * exact ((left_equivalence_unit_iso Hf)^-1).
  - split ; split.
    + use inv_cell_eq ; cbn.
      * apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
        is_iso.
      * apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
        is_iso.
      * cbn.
        rewrite !vassocr.
        exact (internal_triangle1 Hf).
    + use inv_cell_eq ; cbn.
      * apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
        is_iso.
      * apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
        is_iso.
      * cbn.
        rewrite !vassocr.
        exact (internal_triangle2 Hf).
    + cbn.
      apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
      is_iso.
    + cbn.
      apply bicat_is_invertible_2cell_to_op1_bicat_is_invertible_2cell.
      is_iso.
Defined.

Definition op1_bicat_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence
           {C : bicat}
           {X Y : op1_bicat C}
           (f : X --> Y)
  : @left_adjoint_equivalence C Y X f ≃ left_adjoint_equivalence f.
Proof.
  use make_weq.
  - exact (bicat_left_adjoint_equivalence_to_op1_bicat_left_adjoint_equivalence f).
  - use isweq_iso.
    + exact (op1_bicat_left_adjoint_equivalence_to_bicat_left_adjoint_equivalence f).
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

Definition bicat_adjoint_equivalence_is_op1_bicat_adjoint_equivalence
           {C : bicat}
           (X Y : op1_bicat C)
  : @adjoint_equivalence C Y X ≃ adjoint_equivalence X Y.
Proof.
  use weqfibtototal.
  intro α.
  apply op1_bicat_left_adjoint_equivalence_is_bicat_left_adjoint_equivalence.
Defined.
