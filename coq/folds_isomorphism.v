 
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import aux_lemmas.
Require Import folds_precat.
Require Import from_precats_to_folds_and_back.

Local Notation "a ⇒ b" := (folds_morphisms a b)(at level 50).


(** * Definition of FOLDS precat isomorphisms *)

Section folds_iso_def.

Variable C : folds_precat.

Definition folds_iso_data (a b : C) : UU :=
   dirprod (dirprod (∀ {x : C}, weq (x ⇒ a) (x ⇒ b)) 
                    (∀ {z : C}, weq (a ⇒ z) (b ⇒ z))) 
           (weq (a ⇒ a) (b ⇒ b)).

Definition ϕ1 {a b : C} (f : folds_iso_data a b) {x : C} : weq (x ⇒ a) (x ⇒ b) :=
      pr1 (pr1 f) x.
Definition ϕ2 {a b : C} (f : folds_iso_data a b) {z : C} : weq (a ⇒ z) (b ⇒ z) :=
      pr2 (pr1 f) z.
Definition ϕdot {a b : C} (f : folds_iso_data a b) : weq (a ⇒ a) (b ⇒ b) :=
      pr2 f.


(* Notation "'T' f g h" := (comp f g h) (at level 4). *)
Notation "a ≅ b" := (weq a b) (at level 40).

Definition folds_iso_prop {a b : C} (i : folds_iso_data a b) :=
 dirprod(
    dirprod (dirprod (dirprod (∀ x y (f : x ⇒ y) (g : y ⇒ a) (h : x ⇒ a), comp f g h ≅ comp f (ϕ1 i g) (ϕ1 i h))  (* 5.3 *)
                              (∀ x z (f : x ⇒ a) (g : a ⇒ z) (h : x ⇒ z), comp f g h ≅ comp (ϕ1 i f) (ϕ2 i g) h)) (* 5.4 *)
                     (∀ z w (f : a ⇒ z) (g : z ⇒ w) (h : a ⇒ w), comp f g h ≅ comp (ϕ2 i f) g (ϕ2 i h)))          (* 5.5 *)
            (dirprod (dirprod (∀ x (f : x ⇒ a) (g : a ⇒ a) (h : x ⇒ a), comp f g h ≅ comp (ϕ1 i f) (ϕdot i g) (ϕ1 i h))    (* 5.6 *)
                              (∀ x (f : a ⇒ x) (g : x ⇒ a) (h : a ⇒ a), comp f g h ≅ comp (ϕ2 i f) (ϕ1 i g) (ϕdot i h)))   (* 5.7 *)
                     (dirprod (∀ x (f : a ⇒ a) (g : a ⇒ x) (h : a ⇒ x), comp f g h ≅ comp (ϕdot i f) (ϕ2 i g) (ϕ2 i h))    (* 5.8 *)
                              (∀ f g h : a ⇒ a, comp f g h ≅ comp (ϕdot i f) (ϕdot i g) (ϕdot i h))))                      (* 5.9 *)
       )
       (∀ f : a ⇒ a, id f ≅ id (ϕdot i f)).  (* 5.10 *)
 
Definition isaprop_folds_iso_prop (a b : C) (i : folds_iso_data a b) : isaprop (folds_iso_prop i).
Proof.
  repeat (apply isapropdirprod);
   repeat (apply impred; intro); apply isapropweqtoprop; apply pr2.
Qed.

Definition folds_iso (a b : C) := total2 
      (λ i : folds_iso_data a b, folds_iso_prop i).

Definition folds_iso_data_from_folds_iso (a b : C) :  
  folds_iso a b → folds_iso_data a b := λ i, pr1 i.
Coercion folds_iso_data_from_folds_iso : folds_iso >-> folds_iso_data.

Section from_iso_to_folds_iso.

Variables a b : C.
Variable f : iso (C:=precat_from_folds C) a b.

Definition folds_iso_data_from_iso : folds_iso_data a b :=
  dirprodpair (dirprodpair (iso_comp_left_weq f) 
                           (iso_comp_right_weq (iso_inv_from_iso f))) 
              (iso_conjug_weq f).

Lemma folds_iso_data_prop : folds_iso_prop folds_iso_data_from_iso.
Proof.
  repeat split; intros.
  - simpl. apply logeqweq. 
    + intro H. apply comp_compose2. 
      rewrite assoc. set (H2 := comp_compose2' H). rewrite H2.
      apply idpath.
    + intro H. apply comp_compose2.
      set (H2 := comp_compose2' H).
      rewrite assoc in H2.
      eapply post_comp_with_iso_is_inj. 
      apply f. apply H2.
  - simpl. apply logeqweq.
    + intro H. apply comp_compose2.
      apply pathsinv0. etransitivity.
      * apply (pathsinv0 (comp_compose2' H)).
      * transitivity (compose (compose (C:=precat_from_folds C)  f0 (compose f (inv_from_iso f))) g).   rewrite iso_inv_after_iso. rewrite id_right. apply idpath.
        repeat rewrite assoc; apply idpath.
    + intro H. apply comp_compose2.
      set (H2 := comp_compose2' H). apply pathsinv0.
      etransitivity. 
      * apply (pathsinv0 H2).
      * transitivity (compose (compose (C:=precat_from_folds C)  f0 (compose f (inv_from_iso f))) g).   
        repeat rewrite assoc; apply idpath.
        rewrite iso_inv_after_iso. rewrite id_right. apply idpath.
  - simpl. apply logeqweq. 
    + intro H. apply comp_compose2. 
      rewrite <- assoc. rewrite (comp_compose2' H). apply idpath.
    + intro H. apply comp_compose2.
      set (H2:= comp_compose2' H).
      rewrite <- assoc in H2.
      set (H3:= pre_comp_with_iso_is_inj _  _ _ _ _ (is_iso_inv_from_iso _ _ f) _ _ H2). 
      assumption.
  - simpl; apply logeqweq. 
    + intro H; apply comp_compose2.
      rewrite <- (comp_compose2' H).
      transitivity 
  (compose (compose (C:=precat_from_folds C) f0 (compose (C:=precat_from_folds C) f (inv_from_iso f)))(compose (C:=precat_from_folds C) g  f)).
      * repeat rewrite assoc; apply idpath.
      * rewrite iso_inv_after_iso. rewrite id_right; apply assoc.
    + intro H; apply comp_compose2.
      set (H2 := comp_compose2' H).
      repeat rewrite assoc in H2.
      set (H3:= post_comp_with_iso_is_inj _  _ _ _ (pr2 f) _  _ _ H2). 
      rewrite <- H3; clear H3 H2 H.
      transitivity 
   (compose (compose (C:=precat_from_folds C) f0 (compose (C:=precat_from_folds C) f (inv_from_iso f))) g).
      * rewrite iso_inv_after_iso, id_right; apply idpath.
      * repeat rewrite assoc; apply idpath.
  -  simpl; apply logeqweq.
    + intro H. apply comp_compose2.
      repeat rewrite assoc; rewrite assoc4.
      rewrite (comp_compose2' H).
      apply pathsinv0, assoc.
    + intro H; apply comp_compose2.
      set (H2 := comp_compose2' H).
      rewrite <- assoc in H2.
      set (H3 := pre_comp_with_iso_is_inj _ _ _  _ _ ((is_iso_inv_from_iso  _ _ f)) _ _ H2).
      rewrite assoc in H3.
      set (H4:= post_comp_with_iso_is_inj _ _ _ _ (pr2 f) _ _ _ H3).
      assumption.
  - simpl. apply logeqweq.
    + intro H; apply comp_compose2.
      rewrite <- (comp_compose2' H); clear H.
      repeat rewrite <- assoc. apply maponpaths. repeat rewrite assoc.      
      rewrite assoc4, iso_inv_after_iso, id_right.
      apply idpath.
    + intro H; apply comp_compose2.
      set (H':= comp_compose2' H); generalize H'; clear H' H; intro H.
      repeat rewrite <- assoc in H.
      set (H2:=pre_comp_with_iso_is_inj _ _ _  _ _ ((is_iso_inv_from_iso  _ _ f)) _ _ H); clearbody H2; clear H.
      repeat rewrite  assoc in H2; rewrite assoc4 in H2.
      rewrite iso_inv_after_iso, id_right in H2.
      assumption.
  - simpl; apply logeqweq.
    + intro H; set (H':=comp_compose2' H); clearbody H'; clear H;
      rename H' into H; rewrite <- H; clear H.
      apply comp_compose2.
      repeat rewrite <- assoc; apply maponpaths; simpl.
      set (H':=assoc (precat_from_folds C) _ _ _ _ f0 g f); clearbody H';
      simpl in *. rewrite <- H'; clear H'.
      apply maponpaths. simpl in *. 
      repeat rewrite  (assoc (precat_from_folds C)).
      rewrite iso_inv_after_iso, id_left; 
      apply idpath.
    + intro H; set (H':=comp_compose2' H); clearbody H'; clear H;
      rename H' into H.
      apply comp_compose2.
      repeat rewrite <- assoc in H.
      set (H':=pre_comp_with_iso_is_inj _ _ _  _ _ ((is_iso_inv_from_iso  _ _ f)) _ _ H); clearbody H'; clear H.
      repeat rewrite assoc in H'.
      set (H'':=post_comp_with_iso_is_inj _ _ _ _ (pr2 f) _ _ _ H');
      clearbody H''; clear H'.
      rewrite assoc4, iso_inv_after_iso, id_right in H'';
      assumption.
  - simpl. apply logeqweq.  
    + intro H. apply id_identity2. 
      rewrite (id_identity2' H). rewrite (id_left (precat_from_folds C)).
      apply (iso_after_iso_inv _ _ _ f).
    + intro H. apply id_identity2.
      set (H':=id_identity2' H); clearbody H'; clear H.
      set (H2:=iso_inv_to_left _ _ _ _ f _ _ H'); clearbody H2.
      rewrite id_right in H2.      
      transitivity (compose (C:=precat_from_folds C) f (inv_from_iso f)).
      * apply (iso_inv_on_left (precat_from_folds C)); auto.
      * apply (iso_inv_after_iso (precat_from_folds C)).
Qed.

End from_iso_to_folds_iso.

Section from_folds_iso_to_iso.

Variables a b : C.
Variable i : folds_iso a b.

Let i': a ⇒ b := ϕ1 i (identity (C:=precat_from_folds C) _ ).
Let i'inv : b ⇒ a := ϕ2 i (identity (C:=precat_from_folds C) _ ).

(* before attacking this one, show id and comp for fold_isos


Lemma are_inverse : is_inverse_in_precat (C:=precat_from_folds C) i' i'inv.
Proof.
  split.
  - simpl in *.
    apply id_identity2'.
  admit.
Qed.
*)
  
End from_folds_iso_to_iso.

End folds_iso_def.


