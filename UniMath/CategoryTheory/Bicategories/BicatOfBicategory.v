(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(* ========================================================================= *)
(* Every (pre)bicategory of UniMath.CategoryTheory.WkCatEnrichment is a      *)
(* (pre)bicategory of UniMath.CategoryTheory.Bicategories.Bicat.             *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.prebicategory.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.whiskering.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.Notations.

Local Open Scope cat.

(* ------------------------------------------------------------------------- *)
(* Missing lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma whisker_left_left {C : prebicategory} {a b c d : C}
      (f : a -1-> b) (g : b -1-> c) {h i : c -1-> d} (x : h -2-> i) :
  whisker_left f (whisker_left g x) ;v; associator_2mor f g i =
  associator_2mor f g h ;v; whisker_left (f ;1; g) x.
Proof.
  unfold whisker_left.
  etrans; [ apply associator_naturality | idtac].
  apply maponpaths.
  apply maponpaths_2.
  exact horizontal_comp_id.
Defined.

Lemma whisker_left_right {C : prebicategory} {a b c d : C}
      (f : a -1-> b) (g h : b -1-> c) (i : c -1-> d) (x : g -2-> h) :
  whisker_left f (whisker_right x i) ;v; associator_2mor f h i =
  associator_2mor f g i ;v; whisker_right (whisker_left f x) i.
Proof.
  exact (associator_naturality (identity f) x (identity i)).
Defined.

Lemma whisker_right_right {C : prebicategory} {a b c d : C}
      (f g : a -1-> b) (h : b -1-> c) (i : c -1-> d) (x : f -2-> g) :
  associator_2mor f h i ;v; whisker_right (whisker_right x h) i =
  whisker_right x (h ;1; i) ;v; associator_2mor g h i.
Proof.
  unfold whisker_right.
  etrans; [ apply pathsinv0, associator_naturality | idtac].
  apply maponpaths_2, maponpaths.
  exact horizontal_comp_id.
Defined.

(* ------------------------------------------------------------------------- *)
(* From bicategory structure to bicat structure.                             *)
(* ------------------------------------------------------------------------- *)

Section unfold_data.

Variable C : prebicategory.

Definition bcat_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists C. exact (λ a b, homprecat a b).
Defined.

Definition bcat_cell_struct : prebicat_2cell_struct bcat_precategory_ob_mor
  := λ (a b : C) (f g : homprecat a b), (homprecat a b) ⟦ f, g ⟧.

Definition bcat_ob_mor_cells : ∑ (C : precategory_ob_mor), prebicat_2cell_struct C.
Proof.
  exists bcat_precategory_ob_mor. exact bcat_cell_struct.
Defined.

Definition bcat_1_id_comp_cells : prebicat_1_id_comp_cells.
Proof.
  use tpair.
  - exists bcat_precategory_ob_mor.
    use tpair.
    + simpl. intros. exact (identity1 _).
    + simpl. intros a b c f g. exact (compose1 f g).
  - exact bcat_cell_struct.
Defined.

(*
Definition bcat_cells_1_id_comp : ∑ C : prebicat_ob_mor_cells, precategory_id_comp C.
Proof.
  exists bcat_ob_mor_cells. split.
  - simpl. intros. exact (identity1 _).
  - simpl. intros a b c f g. exact (compose1 f g).
Defined.
 *)

Definition bcat_2_id_comp_struct : prebicat_2_id_comp_struct bcat_1_id_comp_cells.
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
    intros a b c f g1 g2 x. exact (whisker_left f x).
  - (* right whiskering *)
    intros a b c f1 f2 g x. exact (whisker_right x g).
Defined.

Definition bcat_data : ∑ C, prebicat_2_id_comp_struct C.
Proof.
  exists bcat_1_id_comp_cells. exact bcat_2_id_comp_struct.
Defined.


Theorem bcat_laws : prebicat_laws bcat_data.
Proof.
  repeat split;
  unfold id2, vcomp2, runitor, lunitor, rinvunitor, linvunitor,
         rassociator, lassociator, lwhisker, rwhisker;
  simpl;
  unfold bcat_precategory_ob_mor, bcat_cell_struct, bcat_ob_mor_cells,
         bcat_1_id_comp_cells, bcat_2_id_comp_struct, bcat_data;
  simpl;
  first [ intros until 1 | intros ].
  - (* 1a id2_left *)
    apply id_left.
  - (* 1b id2_right *)
    apply id_right.
  - (* 2 vassocr *)
    apply assoc.
  - (* 3a lwhisker_id2 *)
    apply whisker_left_id_2mor.
  - (* 3b id2_rwhisker *)
    apply whisker_right_id_2mor.
  - (* 4 lwhisker_vcomp *)
    apply pathsinv0, whisker_left_on_comp.
  - (* 5 rwhisker_vcomp *)
    apply pathsinv0, whisker_right_on_comp.
  - (* 6  vcomp_lunitor *)
    apply left_unitor_naturality.
  - (* 7 vcomp_runitor *)
    apply right_unitor_naturality.
  - (* 8 lwhisker_lwhisker *)
    apply whisker_left_left.
  - (* 9 rwhisker_lwhisker *)
    apply whisker_left_right.
  - (* 10 rwhisker_rwhisker *)
    apply whisker_right_right.
  - (* 11 vcomp_whisker *)
    apply twomor_naturality.
  - (* 12a lunitor_linvunitor *)
    apply (iso_inv_after_iso (left_unitor f)).
  - (* 12b linvunitor_lunitor *)
    apply (iso_after_iso_inv (left_unitor f)).
  - (* 13a runitor_rinvunitor *)
    apply (iso_inv_after_iso (right_unitor f)).
  - (* 13b rinvunitor_runitor *)
    apply (iso_after_iso_inv (right_unitor f)).
  - (* 14a lassociator_rassociator *)
    apply (iso_inv_after_iso (associator f g h)).
  - (* 14b rassociator_lassociator *)
    apply (iso_after_iso_inv (associator f g h)).
  - (* 15 runitor_rwhisker *)
    apply pathsinv0, (triangle_axiom f g).
  - (* 16  lassociator_lassociator *)
    apply pathsinv0, (pentagon_axiom f g h).
Defined.

Definition bcat : prebicat := (bcat_data,, bcat_laws).

End unfold_data.
