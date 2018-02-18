(* ========================================================================= *)
(* Every prebicategory of UniMath.CategoryTheory.bicategories is a           *)
(* prebicategory of UniMath.CategoryTheory.bicat.                            *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.bicategories.prebicategory.

Require Import UniMath.CategoryTheory.bicat.bicat.

Open Scope cat.

(* ------------------------------------------------------------------------- *)
(* From bicategory structure to bicat structor.                              *)
(* ------------------------------------------------------------------------- *)

Section unfold_data.

Variable C : prebicategory.

Definition bcat_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists C.
  exact (λ a b, homprecat a b).
Defined.

Definition bcat_cell_struct : bicat_cell_struct bcat_precategory_ob_mor
  := λ (a b : C) (f g : homprecat a b), (homprecat a b) ⟦ f, g ⟧.

Definition bcat_ob_mor_cells : ∑ (C : precategory_ob_mor), bicat_cell_struct C.
Proof.
  exists bcat_precategory_ob_mor.
  exact bcat_cell_struct.
Defined.

Definition bcat_cells_1_id_comp : ∑ C : bicat_ob_mor_cells, precategory_id_comp C.
Proof.
  exists bcat_ob_mor_cells. split.
  - simpl. intros. exact (identity1 _).
  - simpl. intros a b c f g. exact (compose1 f g).
Defined.

Definition bcat_2_id_comp_struct : bicat_2_id_comp_struct bcat_cells_1_id_comp.
Proof.
  repeat split; simpl; unfold bcat_cell_struct.
  - (* 2-unit *)
    intros. exact (identity _).
  - (* left unitor *)
    intros. exact (left_unitor f).
  - (* right unitor *)
    intros. exact (right_unitor f).
  - (* left inverse unitor *)
    intros. exact (inv_from_iso (left_unitor f)).
  - (* right inverse unitor *)
    intros. exact (inv_from_iso (right_unitor f)).
  - (* right associator *)
    intros. exact (inv_from_iso (associator f g h)).
  - (* left associator *)
    intros. exact (associator_2mor f g h).
  - (* vertical composition *)
    intros a b f g h x y. exact (x · y).
  - (* left whiskering *)
    intros a b c f g1 g2 x. exact (compose2h (identity f) x).
  - (* right whiskering *)
    intros a b c f1 f2 g x. exact (compose2h x (identity g)).
Defined.

Definition bcat_data : ∑ C, bicat_2_id_comp_struct C.
Proof.
  exists bcat_cells_1_id_comp.
  exact bcat_2_id_comp_struct.
Defined.

Theorem bcat_laws : bicat_laws bcat_data.
Proof.
  repeat split; simpl; unfold bcat_cell_struct, id2, vcomp2, lwhisker, rwhisker; simpl.
  - (* 1a id2_left *)
    intros. use id_left.
  - (* 1b id2_right *)
    intros. use id_right.
  - (* 2 vassocr *)
    intros. apply assoc.
  - (* 3a lwhisker_id2 *)
    intros. use functor_id.
  - (* 3b id2_rwhisker *)
    intros. use functor_id.
  - (* 4 lwhisker_vcomp *)
    intros. unfold compose2h.
    etrans. eapply pathsinv0. apply functor_comp. apply maponpaths.
    apply total2_paths2; simpl.
    + apply id_left.
    + reflexivity.
  - (* 5 rwhisker_vcomp *)
    intros. unfold compose2h.
    etrans. eapply pathsinv0. apply functor_comp. apply maponpaths.
    apply total2_paths2; simpl.
    + reflexivity.
    + apply id_left.
  - (* 6  vcomp_lunitor *)
    intros. unfold compose2h.
    unfold lunitor; simpl.
    unfold compose_functor.
    simpl.
    unfold left_unitor_2mor.
    unfold left_unitor_trans.
    admit.
  - (* 7 vcomp_runitor *)
    admit.
  - (* 8 lwhisker_lwhisker *)
    admit.
  - (* 9 rwhisker_lwhisker *)
    admit.
  - (* 10 rwhisker_rwhisker *)
    admit.
  - (* 11 vcomp_whisker *)
    admit.
  - (* 12a lunitor_linvunitor *)
    admit.
  - (* 12b linvunitor_lunitor *)
    admit.
  - (* 13a runitor_rinvunitor *)
    admit.
  - (* 13b rinvunitor_runitor *)
    admit.
  - (* 14a lassociator_rassociator *)
    admit.
  - (* 14b rassociator_lassociator *)
    admit.
  - (* 15 runitor_rwhisker *)
    admit.
  - (* 16  lassociator_lassociator *)
Admitted.

End unfold_data.
