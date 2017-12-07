

(** Univalent FOLDS

    Benedikt Ahrens, following notes by Michael Shulman

Contents of this file:

  - Map [folds_precat_from_precat]
  - Map [precat_from_folds_precat]
  - Identity [folds_precat_from_precat_precat_from_folds_precat]
  - Identity [precat_from_folds_precat_folds_precat_from_precat]
  - Lemmas to pass between the compositions via predicate [comp] and as function [compose]
  - Lemmas to pass between the identities via predicate [id] and as a function [identity]

*)

Require Import UniMath.Folds.UnicodeNotations.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.Folds.aux_lemmas.
Require Import UniMath.Folds.folds_precat.

Local Open Scope cat.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).

(** * From precategories to FOLDS precategories *)

Section from_precats_to_folds.

Section data.

Variable C : precategory_data.
Variable hsC : has_homsets C.

(** identity as a predicate *)
Definition id_pred {a : C} : a ⇒ a → hProp :=
   λ f, hProppair (f = identity _ ) (hsC a a _ _) .

Lemma id_pred_id (a : C) : id_pred (identity a).
Proof.
  apply idpath.
Qed.

(** composition as a predicate *)
Definition comp_pred {a b c : C} : a ⇒ b → b ⇒ c → a ⇒ c → hProp :=
  λ f g fg, hProppair (compose f g = fg) (hsC _ _ _ _ ).

Lemma comp_pred_comp (a b c : C) (f : a ⇒ b) (g : b ⇒ c) : comp_pred f g (compose f g).
Proof.
  apply idpath.
Defined.

Definition folds_id_comp_from_precat_data : folds_id_T :=
  tpair (λ C : folds_ob_mor, (∏ a : C, a ⇒ a → hProp)
                           × (∏ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp))
        (pr1 C) (dirprodpair (@id_pred) (@comp_pred)).

End data.

Variable C : precategory.
Hypothesis hs: has_homsets C.

(** FOLDS precategory from precategory *)

Definition folds_precat_from_precat : folds_precat.
Proof.
  exists (folds_id_comp_from_precat_data C hs).
  repeat split.
  - intro a.
    apply hinhpr.
    exists (identity a).
    apply idpath.
  - intros; unfold id, T; simpl.
    intermediate_path (compose f (identity _ )).
    + apply maponpaths; assumption.
    + apply id_right.
 - intros; unfold id, T; simpl.
   intermediate_path (compose (identity _ ) f).
   +  rewrite X. apply idpath.
   +  apply id_left.
 - intros a b c f g.
   apply hinhpr.
   exists (compose f g).
   apply idpath.
 - simpl.
   intros a b c f g h k H1 H2.
   intermediate_path (compose f g).
   + apply pathsinv0. apply H1.
   + apply H2.
 - simpl. intros a b c d f g h fg gh fg_h f_gh H1 H2 H3 H4.
   rewrite <- H4, <- H3, <- H2, <- H1.
   apply assoc.
Defined.

End from_precats_to_folds.

(** * From FOLDS precategories to precategories *)

Section from_folds_to_precats.

Variable C : folds_precat.

(** precategory from FOLDS precategory *)

Definition precat_from_folds_data : precategory_data :=
  tpair (λ C : precategory_ob_mor, precategory_id_comp C)
    (pr1 (pr1 C)) (dirprodpair (I_func C)(@T_func C)).

Lemma is_precategory_precat_from_folds_data :
   is_precategory precat_from_folds_data.
Proof.
  repeat split.
  - apply T_I_r.
  - apply T_I_l.
  - apply T_assoc.
Qed.

Definition precat_from_folds_precat : precategory :=
  tpair _ _ is_precategory_precat_from_folds_data.

End from_folds_to_precats.

(** * From FOLDS precats to precats to FOLDS precats *)

Lemma folds_precat_from_precat_precat_from_folds_precat
  (C : folds_precat)(hs:has_folds_homsets C):
    folds_precat_from_precat (precat_from_folds_precat C) hs = C.
Proof.
  apply subtypeEquality'.
  Focus 2.
  - intro a; apply isapropdirprod.
    + apply isaprop_folds_ax_id.
    Focus 2. apply isaprop_folds_ax_T. apply hs.
  - set (Hid := I_contr C).
    set (Hcomp := T_contr C).
    destruct C as [Cd CC]; simpl in *.
    destruct Cd as [Ca Cb]; simpl in *.
    unfold folds_id_comp_from_precat_data.
    apply maponpaths.
    destruct CC as [C1 C2]. simpl in *.
    destruct Cb as [Cid Ccomp]. simpl in *.
    apply pathsdirprod.
    +  apply funextsec.  intro a.
       apply funextsec. intro f. unfold id_pred.  simpl.
       apply subtypeEquality.
       { intro. apply isapropisaprop. }
       simpl.
       apply weqtopaths.
       apply weqimplimpl.
       * intro H. rewrite H.
         set (Hid' := pr1 (Hid a)).
         apply (pr2 (Hid')).
       * intro H. unfold precategory_morphisms in f.
         set (H2 := pr2 (Hid a)). simpl in H2.
         apply (path_to_ctr). assumption.
       * apply hs. (* apply (pr2 (precategory_morphisms _ _ )). *)
       * apply (pr2 (Cid a f)).
   + apply funextsec; intro a.
     apply funextsec; intro b.
     apply funextsec; intro c.
     apply funextsec; intro f.
     apply funextsec; intro g.
     apply funextsec; intro fg.
     clear Hid.
     apply subtypeEquality.
     { intro; apply isapropisaprop. }
     apply weqtopaths. apply weqimplimpl.
       * intro H. simpl in *. rewrite <- H.
         apply (pr2 (pr1 (Hcomp a b c f g))).
       * simpl. intro H. apply pathsinv0. apply path_to_ctr.
           assumption.
       * simpl in *. apply hs. (* apply (pr2 (precategory_morphisms _ _ )). *)
       * apply (pr2 (Ccomp _ _ _ _ _ _ )).
Qed.

(** * From precats to FOLDS precats to precats *)

Lemma precat_from_folds_precat_folds_precat_from_precat (C : precategory)(hs: has_homsets C) :
     precat_from_folds_precat (folds_precat_from_precat C hs) = C.
Proof.
  apply subtypeEquality'.
  Focus 2. intro; apply isaprop_is_precategory. assumption.

  destruct C as [Cdata Cax]; simpl in *.
  destruct Cdata as [Cobmor Cidcomp]; simpl in *.
  unfold precat_from_folds_data.
  simpl.
  apply maponpaths.
  destruct Cidcomp as [Cid Ccomp]; simpl in *.
  apply pathsdirprod.
  - apply funextsec; intro a.
    apply pathsinv0.
    apply path_to_ctr.
    apply idpath.
  - apply funextsec; intro a.
    apply funextsec; intro b.
    apply funextsec; intro c.
    apply funextsec; intro f.
    apply funextsec; intro g.
    apply pathsinv0.
    apply path_to_ctr.
    apply idpath.
Qed.

(** * Some lemmas to pass from [comp] to [compose] and back **)

Local Notation "C ^" := (folds_precat_from_precat C) (at level 3).
Local Notation "C ^^" := (precat_from_folds_precat C) (at level 3).

Lemma comp_compose {C : precategory} (hs: has_homsets C) {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h : a ⇒ c} :
   f · g = h -> T (C:=C^hs) f g h.
Proof.
   apply (λ x, x).
Qed.
Lemma comp_compose' {C : precategory} (hs: has_homsets C){a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h : a ⇒ c} :
    T (C:=C^hs) f g h -> f · g = h.
Proof.
   apply (λ x, x).
Qed.

Lemma comp_compose2 {C : folds_precat} {a b c : C}
  {f : folds_morphisms a b} {g : folds_morphisms b c} {h : folds_morphisms a c} :
   compose (C:= C^^) f g = h -> T f g h.
Proof.
  intro H; rewrite <- H. apply T_func_T.
Qed.

Lemma comp_compose2' {C : folds_precat} {a b c : C}
  {f : folds_morphisms a b} {g : folds_morphisms b c} {h : folds_morphisms a c} :
  T f g h -> compose (C:=C^^) f g = h.
Proof.
  intro H. apply pathsinv0. apply path_to_ctr. assumption.
Qed.


(** * Some lemmas to pass from [id] to [identity] and back **)

Lemma id_identity {C : precategory} (hs: has_homsets C){a : C} {f : a ⇒ a} : f = identity _ -> I (C:=C^hs) f.
Proof.
  apply (λ x, x).
Qed.

Lemma id_identity' {C : precategory} (hs: has_homsets C){a : C} {f : a ⇒ a} : I (C:=C^hs) f -> f = identity _ .
Proof.
  apply (λ x, x).
Qed.

Lemma id_identity2 {C : folds_precat} {a : C} {f : a ⇒ a} : f = identity (C:=C^^)  _ -> I f.
Proof.
  intro H; rewrite H.
  apply I_func_I.
Qed.

Lemma id_identity2' {C : folds_precat} {a : C} {f : a ⇒ a} : I f -> f = identity (C:=C^^) _ .
Proof.
  intro H. apply path_to_ctr; assumption.
Qed.
