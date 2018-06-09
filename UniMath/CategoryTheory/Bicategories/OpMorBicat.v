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

(* Todo: duplicated theorems:
   is_invertible_2cell_lassociator
   is_invertible_2cell_lassociator
 *)

(* TODO: Compare with lwhisker_lwhisker vs lwhisker_lwhisker_rassociator. *)
Lemma rwhisker_rwhisker_alt {C : prebicat} {a b c d : C}
      (f : C ⟦ b, a ⟧) (g : C ⟦ c, b ⟧) {h i : C ⟦ d, c ⟧} (x : h ==> i)
  : ((x ▹ g) ▹ f) • rassociator i g f = rassociator h g f • (x ▹ g · f).
Proof.
  apply inv_2cell_left_cancellable with (lassociator h g f).
  { apply is_invertible_2cell_lassociator. }
  etrans. { apply vassocr. }
  etrans. { apply maponpaths_2, rwhisker_rwhisker. }
  etrans. { apply vassocl. }
  etrans. { apply maponpaths, lassociator_rassociator. }
  apply pathsinv0.
  etrans. { apply vassocr. }
  etrans. { apply maponpaths_2, lassociator_rassociator. }
  etrans.
  - apply id2_left.
  - apply pathsinv0, id2_right.
Qed.

Lemma rassociator_rassociator
      {C : prebicat} {a b c d e : C}
      (f : C ⟦ a, b ⟧) (g : C ⟦ b, c ⟧) (h : C ⟦ c, d ⟧) (i : C ⟦ d, e ⟧)
  : ((rassociator f g h ▹ i) • rassociator f (g · h) i) • (f ◃ rassociator g h i) =
    rassociator (f · g) h i • rassociator f g (h · i).
Proof.
  apply inv_2cell_left_cancellable with (lassociator (f · g) h i).
  { apply is_invertible_2cell_lassociator. }
  apply inv_2cell_left_cancellable with (lassociator f g (h · i)).
  { apply is_invertible_2cell_lassociator. }
  etrans. { apply vassocr. }
  etrans.
  { apply maponpaths_2, pathsinv0.
    apply lassociator_lassociator. }
  etrans. { apply vassocl. }
  etrans.
  { apply maponpaths.
    etrans.
    { apply maponpaths, vassocl. }
    etrans. { apply vassocr. }
    apply maponpaths_2.
    etrans. { apply rwhisker_vcomp. }
    apply maponpaths, lassociator_rassociator.
  }
  apply pathsinv0.
  etrans.
  { apply maponpaths.
    etrans. { apply vassocr. }
    etrans. { apply maponpaths_2, lassociator_rassociator. }
    apply id2_left. }
  etrans.
  apply lassociator_rassociator.
  apply pathsinv0.
  etrans.
  { apply maponpaths.
    etrans.
    { apply vassocr. }
    apply maponpaths_2.
    etrans. { apply maponpaths_2, id2_rwhisker. }
    apply id2_left.
  }
  etrans.
  apply vassocl.
  etrans.
  apply maponpaths.
  etrans.
  apply vassocr.
  etrans.
  apply maponpaths_2.
  apply lassociator_rassociator.
  apply id2_left.
  etrans.
  apply lwhisker_vcomp.
  etrans.
  apply maponpaths.
  apply lassociator_rassociator.
  apply lwhisker_id2.
Qed.

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
