
(** * Examples 

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- arrow precategories
- objects with N-actions
- elements, over hSet

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.

Local Open Scope mor_disp_scope.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** ** The displayed arrow category 

A very fertile example: many others can be obtained from it by reindexing. *)
Section Arrow_Disp.

Context (C:Precategory).

Definition arrow_disp_ob_mor : disp_precat_ob_mor (C × C).
Proof.
  exists (fun xy : (C × C) => (pr1 xy) --> (pr2 xy)).
  simpl; intros xx' yy' g h ff'. 
    exact (pr1 ff' ;; h = g ;; pr2 ff')%mor.
Defined.

Definition arrow_id_comp : disp_precat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_precat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_precat_axioms (C × C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition arrow_disp : disp_precat (C × C)
  := (arrow_data ,, arrow_axioms).

End Arrow_Disp.

(** ** Objects with N-action

For any category C, “C-objects equipped with an N-action” (or more elementarily, with an endomorphism) form a displayed category over C 
Section ZAct. 

Once we have pullbacks of displayed precategories, this can be obtained as a pullback of the previous example. *)

Section NAction.

Context (C:Precategory).

Definition NAction_disp_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => c --> c).
  intros x y xx yy f. exact (f ;; yy = xx ;; f)%mor.
Defined.

Definition NAction_id_comp : disp_precat_id_comp C NAction_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition NAction_data : disp_precat_data C
  := (NAction_disp_ob_mor ,, NAction_id_comp).

Lemma NAction_axioms : disp_precat_axioms C NAction_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition NAction_disp : disp_precat C
  := (NAction_data ,, NAction_axioms).

End NAction.

(** ** Elements of sets

A presheaf on a (pre)category can be viewed as a fiberwise discrete displayed (pre)category. In fact, the universal example of this is the case corresponding to the identity functor on [SET].  So, having given the displayed category for this case, one obtains it for arbitrary presheaves by reindexing. *)

(* TODO: move? ponder? *)
Local Notation SET := Precategories.SET.

Section Elements_Disp.

Definition elements_ob_mor : disp_precat_ob_mor SET.
Proof.
  use tpair.
  - simpl. exact (fun X => X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_precat_id_comp SET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_precat_data SET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_precat_axioms SET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_precat SET
  := (_ ,, elements_axioms).

Definition disp_precat_of_elements {C : Precategory} (P : functor C SET)
  := reindex_disp_precat P elements_universal.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : Precategory} (P : functor C SET)
  := total_precat (disp_precat_of_elements P).

End Elements_Disp.
