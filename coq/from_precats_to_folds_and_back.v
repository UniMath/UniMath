
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.FOLDS.aux_lemmas.
Require Import RezkCompletion.FOLDS.folds_precat.


(** * From precategories to FOLDS precategories *)

Section from_precats_to_folds.

Local Notation "a ⇒ b" := (precategory_morphisms a b)(at level 50).

Section data.

Variable C : precategory_data.

Definition id_pred {a : C} : a ⇒ a → hProp :=
   λ f, hProppair (f == identity _ ) (pr2 (a ⇒ a) _ _ ) .

Lemma id_pred_id (a : C) : id_pred (identity a).
Proof.
  apply idpath.
Qed.

Definition comp_pred {a b c : C} : a ⇒ b → b ⇒ c → a ⇒ c → hProp :=
  λ f g fg, hProppair (compose f g == fg) (pr2 (_ ⇒ _ ) _ _ ).

Lemma comp_pred_comp (a b c : C) (f : a ⇒ b) (g : b ⇒ c) : comp_pred f g (compose f g).
Proof.
  apply idpath.  
Defined.

Definition folds_id_comp_from_precat_data : folds_id_comp :=
  tpair (λ C : folds_ob_mor, dirprod (∀ a : C, a ⇒ a → hProp)
            (∀ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp))  
        (pr1 C) (dirprodpair (@id_pred) (@comp_pred)).

End data.

Variable C : precategory.

Definition folds_precat_from_precat : folds_precat.
Proof.
  exists (folds_id_comp_from_precat_data C).
  repeat split.
  - intro a.
    apply hinhpr.
    exists (identity a).
    apply idpath.
  - intros; unfold id, comp; simpl.
    transitivity (compose f (identity _ )).
    + apply maponpaths; assumption.
    + apply id_right.
 - intros; unfold id, comp; simpl.
   transitivity (compose (identity _ ) f).
   +  rewrite X. apply idpath.
   +  apply id_left.
 - intros a b c f g.
   apply hinhpr.
   exists (compose f g).
   apply idpath.
 - simpl. 
   intros a b c f g h k H1 H2.
   transitivity (compose f g); auto.
 - simpl. intros a b c d f g h fg gh fg_h f_gh H1 H2 H3 H4.
   rewrite <- H4, <- H3, <- H2, <- H1. 
   apply assoc.
Defined.

End from_precats_to_folds.

(** * From FOLDS precategories to precategories *)

Section from_folds_to_precats.

Variable C : folds_precat.

Definition precat_from_folds_data : precategory_data :=
  tpair (λ C : precategory_ob_mor, precategory_id_comp C)
    (pr1 (pr1 C)) (dirprodpair (id_func C)(@comp_func C)).

Lemma is_precategory_precat_from_folds_data : 
   is_precategory precat_from_folds_data.
Proof.
  repeat split.
  - apply comp_id_r.  
  - apply comp_id_l. 
  - apply comp_assoc. 
Qed.

Definition precat_from_folds : precategory := 
  tpair _ _ is_precategory_precat_from_folds_data.

End from_folds_to_precats.

(** * From FOLDS precats to precats to FOLDS precats *)

Lemma folds_precat_from_precat_precat_from_folds (C : folds_precat) : 
    folds_precat_from_precat (precat_from_folds C) == C.
Proof.
  apply total2_paths_hProp.
  - intro a; apply isapropdirprod.
    + apply isaprop_folds_ax_id.
    + apply isaprop_folds_ax_comp.
  - set (Hid := id_contr C).
    set (Hcomp := comp_contr C).
    destruct C as [Cd CC]; simpl in *.
    destruct Cd as [Ca Cb]; simpl in *. 
    unfold folds_id_comp_from_precat_data.
    apply maponpaths.
    destruct CC as [C1 C2]. simpl in *. 
    destruct Cb as [Cid Ccomp]. simpl in *. 
    apply pathsdirprod.
    +  apply funextsec.  intro a.
       apply funextsec. intro f. unfold id_pred.  simpl. 
       apply total2_paths_hProp.
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
       * apply (pr2 (precategory_morphisms _ _ )).
       * apply (pr2 (Cid a f)).
   + apply funextsec; intro a.
     apply funextsec; intro b.
     apply funextsec; intro c.
     apply funextsec; intro f.
     apply funextsec; intro g.
     apply funextsec; intro fg.
     clear Hid.
     apply total2_paths_hProp.
     { intro; apply isapropisaprop. } 
     apply weqtopaths. apply weqimplimpl.
       * intro H. simpl in *. rewrite <- H.
         apply (pr2 (pr1 (Hcomp a b c f g))).
       * simpl. intro H. apply pathsinv0. apply path_to_ctr.
           assumption.
       * simpl in *. apply (pr2 (precategory_morphisms _ _ )).
       * apply (pr2 (Ccomp _ _ _ _ _ _ )).
Qed.

(** * From precats to FOLDS precats to precats *)

Lemma precat_from_folds_folds_precat_from_precat (C : precategory) : 
     precat_from_folds (folds_precat_from_precat C) == C.
Proof.
  apply total2_paths_hProp.
  { intro; apply isaprop_is_precategory. }
  destruct C as [Cdata Cax]; simpl in *.
  destruct Cdata as [Cobmor Cidcomp]; simpl in *.
  unfold precat_from_folds_data; apply maponpaths.
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

