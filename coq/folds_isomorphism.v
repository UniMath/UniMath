
(** Univalent FOLDS

    Benedikt Ahrens, following notes by Michael Shulman

Contents of this file:

  - Definition of isomorphism in a FOLDS precategory [folds_iso]
  - Components [φ2] and [φdot] are determined by [φ1]
  - Identity isomorphim, inverse and composition
  - Map [folds_iso_from_iso] associating to any FOLDS precat isomorphism
    an isomorphism in the corresponding precategory à la RezkCompletion
  - Map [iso_from_iso_folds] doing the converse, still departing from a FOLDS precategory
  - Lemma: [folds_iso_from_iso] and [iso_from_iso_folds] are inverse to each other

*)
 
Require Import UnicodeNotations.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Import uu0.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import aux_lemmas.
Require Import folds_precat.
Require Import from_precats_to_folds_and_back.

Local Notation "a ⇒ b" := (folds_morphisms a b)(at level 50).


(** * Definition of FOLDS precat isomorphisms **)

Section folds_iso_def.

Variable C : folds_precat.
Notation C':= (precat_from_folds_precat C).

Definition folds_iso_data (a b : C) : UU :=
  ((∀ {x : C}, (x ⇒ a) ≃ (x ⇒ b)) 
 × (∀ {z : C}, (a ⇒ z) ≃ (b ⇒ z))) 
×             ((a ⇒ a) ≃ (b ⇒ b)).

Definition ϕ₁ {a b : C} (f : folds_iso_data a b) {x : C} : (x ⇒ a) ≃ (x ⇒ b) :=
      pr1 (pr1 f) x.
Definition ϕ₂ {a b : C} (f : folds_iso_data a b) {z : C} : (a ⇒ z) ≃ (b ⇒ z) :=
      pr2 (pr1 f) z.
Definition ϕo {a b : C} (f : folds_iso_data a b) : (a ⇒ a) ≃ (b ⇒ b) :=
      pr2 f.


Definition folds_iso_prop {a b : C} (i : folds_iso_data a b) :=
 dirprod(
  dirprod(
   dirprod(
    dirprod(
     ∀ x y (f : x ⇒ y) (g : y ⇒ a) (h : x ⇒ a), T f g h ≃ T f (ϕ₁ i g) (ϕ₁ i h))  (* 5.3 *)
     (∀ x z (f : x ⇒ a) (g : a ⇒ z) (h : x ⇒ z), T f g h ≃ T (ϕ₁ i f) (ϕ₂ i g) h)) (* 5.4 *)
      (∀ z w (f : a ⇒ z) (g : z ⇒ w) (h : a ⇒ w), T f g h ≃ T (ϕ₂ i f) g (ϕ₂ i h)))          (* 5.5 *)
       (dirprod (dirprod (∀ x (f : x ⇒ a) (g : a ⇒ a) (h : x ⇒ a), T f g h ≃ T (ϕ₁ i f) (ϕo i g) (ϕ₁ i h))    (* 5.6 *)
                              (∀ x (f : a ⇒ x) (g : x ⇒ a) (h : a ⇒ a), T f g h ≃ T (ϕ₂ i f) (ϕ₁ i g) (ϕo i h)))   (* 5.7 *)
                     (dirprod (∀ x (f : a ⇒ a) (g : a ⇒ x) (h : a ⇒ x), T f g h ≃ T (ϕo i f) (ϕ₂ i g) (ϕ₂ i h))    (* 5.8 *)
                              (∀ f g h : a ⇒ a, T f g h ≃ T (ϕo i f) (ϕo i g) (ϕo i h))))                      (* 5.9 *)
       )
       (∀ f : a ⇒ a, I f ≃ I (ϕo i f)).  (* 5.10 *)
 
Definition isaprop_folds_iso_prop (a b : C) (i : folds_iso_data a b) : isaprop (folds_iso_prop i).
Proof.
  repeat (apply isapropdirprod);
   repeat (apply impred; intro); apply isapropweqtoprop; apply pr2.
Qed.

Definition folds_iso (a b : C) := total2 
      (λ i : folds_iso_data a b, folds_iso_prop i).

Definition folds_iso_data_from_folds_iso {a b : C} :  
  folds_iso a b → folds_iso_data a b := λ i, pr1 i.
Coercion folds_iso_data_from_folds_iso : folds_iso >-> folds_iso_data.

Lemma folds_iso_eq {a b : C} (i i' : folds_iso a b) : 
  folds_iso_data_from_folds_iso i = folds_iso_data_from_folds_iso i' →
   i = i'.
Proof.
  intro H.
  apply total2_paths_hProp.
  - apply isaprop_folds_iso_prop.
  - assumption.
Qed.

(** * Lemmas about FOLDS isomorphisms *)  
(** the families of equivalences constituting a FOLDS isomorphism 
are given by composition **)

Section about_folds_isos.

Context {a b : C}.

Section fix_a_folds_iso.

Variable (i : folds_iso a b).

Lemma ϕ₁_is_comp (x : C) (f : x ⇒ a) : 
    ϕ₁ i f = compose (C:= C') f (ϕ₁ i (identity (C:= C') _ )).
Proof.
  set (q:=pr1 (pr1 (pr1 (pr1 (pr2 i))))). 
  specialize (q _ _ f (identity (C:= C') _ ) f).
  set (q':=pr1 q ); clearbody q'.
  assert (H: T f (identity (C:= C') a) f).
  { set (H:= pr1 (pr2 (pr1 (pr2 C)))). 
    apply H. apply I_func_I. } 
  set (q'H:= q' H). clearbody q'H; clear H q' q.
  apply path_to_ctr. assumption.
Qed.  

Lemma ϕ₂_is_comp (z : C) (g : a ⇒ z) : 
    ϕ₂ i g = compose (C:= C') (ϕ₂ i (identity (C:=C') _ )) g.
Proof.
  set (q:=pr2 (pr1 (pr1 (pr2 i)))). simpl in q.
  specialize (q _ _ (identity (C:= C') _ ) g g).
  set (q':=pr1 q ); clearbody q'.
  assert (H: T (identity (C:= C') a) g g).
  { set (H:= pr2 (pr2 (pr1 (pr2 C)))). 
    apply H. apply I_func_I. } 
  set (q'H:= q' H). clearbody q'H; clear H q' q.
  apply path_to_ctr. assumption.
Qed. 

Lemma ϕ₁_ϕ₂_id : 
 compose (C:=C') (ϕ₁ i (identity (C:=C') _ )) 
                 (ϕ₂ i (identity (C:=C') _ )) = identity _.
Proof.               
  set (q:=pr2 (pr1 (pr1 (pr1 (pr2 i))))). simpl in q.
  specialize (q _ _ (identity (C:= C') _ ) (identity (C:=C')_ ) 
                            (identity (C:=C')_ )).
  set (q':=pr1 q ); clearbody q'.
  apply comp_compose2'.
  apply q'.
  apply comp_compose2.
  apply T_I_l.
Qed.
  
Lemma ϕo_id : 
   ϕo i (identity (C:=C') _ ) = identity (C:=C') _ .
Proof.
  apply id_identity2'.  
  apply (pr2 (pr2 i)).
  apply I_func_I.
Qed.

Lemma ϕ₂_ϕ₁_id: compose (C:=C') 
    ((ϕ₂ i) (identity (C:=C') a)) 
    ((ϕ₁ i) (identity (C:=C') a)) = identity (C:=C') b.
Proof.
  set (H':= pr2 (pr1 (pr2 (pr1 (pr2 i))))).
  simpl in H'.
  specialize (H' _ (identity(C:=C') _ ) 
                     (identity(C:=C') _ )
                     (identity(C:=C') _ )).
  simpl in H'.
  rewrite <- ϕo_id. 
  apply comp_compose2'.
  apply H'.
  apply comp_compose2.
  apply T_I_l.
Qed.

Lemma ϕ₁_ϕ₂_are_inverse : is_inverse_in_precat (C:= C') 
     (ϕ₁ i (identity (C:=C') _ )) (ϕ₂ i (identity (C:=C') _ )).
Proof.
  split.
  - apply ϕ₁_ϕ₂_id.
  - apply ϕ₂_ϕ₁_id.
Qed.

Lemma ϕo_ϕ₁_ϕ₂ (f : a ⇒ a) : 
  ϕo i f = compose 
                 (compose (C:=C') (ϕ₂ i (identity (C:=C') _ )) f) 
                 (ϕ₁ i (identity (C:=C') _) ).
Proof.
  set (q:=pr2 (pr1 (pr2 (pr1 (pr2 i))))); simpl in q; clearbody q.
  specialize (q _ f (identity (C:=C') _ ) f).
  set (q':=pr1 q). clearbody q'. simpl in q'. clear q.
  match goal with | [_ : ?a → _ |- _ ] => assert a end.
  { apply comp_compose2. apply (id_right C'). }
  specialize (q' X). clear X.
  set (q:= comp_compose2' q'). clearbody q; clear q'.
  simpl in *.
  change (ϕo i f) with (ϕo (pr1 i) f). 
  rewrite <- q. clear q.
  rewrite ϕ₂_is_comp. apply idpath.
Qed.

End fix_a_folds_iso.

(** * A FOLDS isomorphism is determined by the first family of isos **) 

Variables i i' : folds_iso a b.

Hypothesis H : ϕ₁ i (identity (C:=C') _ ) = ϕ₁ i' (identity (C:=C') _ ).

Lemma ϕ₂_determined : ∀ x (f : a ⇒ x) , ϕ₂ i f = ϕ₂ i' f.
Proof.
  intros x f.
  rewrite (ϕ₂_is_comp i).
  rewrite (ϕ₂_is_comp i').
  assert (H': is_inverse_in_precat (C:=C') (ϕ₁ i (identity (C:=C')_ )) 
                               (ϕ₂ i' (identity (C:=C') _ ))).
  { split.
    - rewrite H. apply ϕ₁_ϕ₂_id.
    - rewrite H. apply ϕ₂_ϕ₁_id. } 
  assert (X : ϕ₂ i (identity (C:=C') _ ) = ϕ₂ i' (identity (C:=C') _ )).
  { set (H1:= inverse_unique_precat C' _ _  _ _  _ (ϕ₁_ϕ₂_are_inverse i) H').
    assumption.
  } 
  rewrite X.
  apply idpath.
Qed.

Lemma ϕo_determined : ∀ f, ϕo i f = ϕo i' f.
Proof.
  intro f.
  do 2 rewrite ϕo_ϕ₁_ϕ₂.
  rewrite ϕ₂_determined.
  rewrite H.
  apply idpath.
Qed.


Lemma folds_iso_equal : i = i'.
Proof.
  apply folds_iso_eq.
  apply dirprodpath.
  - apply dirprodpath.
    + apply funextsec; intro.
      apply total2_paths_hProp.
      * intros; apply isapropisweq.
      * apply funextfunax; intro f.
        etransitivity.
        { apply ϕ₁_is_comp. }
        symmetry.
        etransitivity.
        { apply ϕ₁_is_comp. } 
        rewrite H. apply idpath.
    + apply funextsec; intro.
      apply total2_paths_hProp.
      * intros; apply isapropisweq.
      * apply funextfunax. apply ϕ₂_determined.
  - apply total2_paths_hProp.
    intros. apply isapropisweq.
    apply funextfunax. intros. 
    apply ϕo_determined.
Qed.  

  
End about_folds_isos.


(** * Identity FOLDS isomorphism **) 


Definition id_folds_iso_data (a : C) : folds_iso_data a a.
Proof.
  repeat split.
  - intro x. apply idweq.
  - intro z. apply idweq.
  - apply idweq.
Defined.

Lemma id_folds_iso_prop (a : C) : folds_iso_prop (id_folds_iso_data a).
Proof.
  repeat split; intros; apply idweq.
Qed.
  
Definition id_folds_iso (a : C) : folds_iso a a := 
  tpair _ (id_folds_iso_data a) (id_folds_iso_prop a).

(** * Inverse of a FOLDS isomorphism **)

Section folds_iso_inverse.

Context {a b : C} (i : folds_iso a b).

Definition folds_iso_inv_data : folds_iso_data b a.
Proof.
  repeat split.
  - intro x. exact (invweq (ϕ₁ i)).
  - intro z. exact (invweq (ϕ₂ i)).
  - exact (invweq (ϕo i)).
Defined.


Lemma folds_iso_inv_prop : folds_iso_prop folds_iso_inv_data.
Proof.
  repeat split; intros.
  - simpl. apply invweq.
    set (q:=pr1 (pr1 (pr1 (pr1 (pr2 i))))). clearbody q.
    set (q':= q _ _ f (invmap (ϕ₁ i) g) (invmap (ϕ₁ i) h)).
    repeat rewrite (homotweqinvweq (ϕ₁ i)) in q'.
    apply q'.
  - simpl. apply invweq.
    set (q:=pr2 (pr1 (pr1 (pr1 (pr2 i))))). simpl in q; clearbody q.
    set (q':= q _ _ (invmap (ϕ₁ i) f) (invmap (ϕ₂ i) g) h); clearbody q'.
    repeat rewrite homotweqinvweq in q'.
    apply q'.
  - simpl. apply invweq.
    set (q:= ((pr2 (pr1 (pr1 (pr2 i)))))). clearbody q; simpl in q.
    set (q':= q _ _ (invmap (ϕ₂ i) f) g  (invmap (ϕ₂ i) h) ).
    repeat rewrite homotweqinvweq in q'.
    apply q'.
  - simpl; apply invweq.
    set (q:= pr1 (pr1 (pr2 (pr1 (pr2 i))))). clearbody q; simpl in q.
    set (q':= q _  (invmap (ϕ₁ i) f) (invmap (ϕo i) g) (invmap (ϕ₁ i) h)).
    repeat rewrite homotweqinvweq in q'.
    apply q'.
  - simpl; apply invweq.
    set (q:= pr2 (pr1 (pr2 (pr1 (pr2 i))))). clearbody q; simpl in q.
    set (q':= q _ (invmap (ϕ₂ i) f) (invmap (ϕ₁ i) g) (invmap (ϕo i) h)).
    repeat rewrite homotweqinvweq in q'.
    apply q'.
  - simpl. apply invweq.
    set (q:= pr1 (pr2 (pr2 (pr1 (pr2 i))))). clearbody q; simpl in q.
    specialize (q _ (invmap (ϕo i) f) (invmap (ϕ₂ i) g) (invmap (ϕ₂ i) h)).
    repeat rewrite homotweqinvweq in q.
    apply q.
  - simpl. apply invweq.
    set (q:= pr2 (pr2 (pr2 (pr1 (pr2 i))))). clearbody q; simpl in q.
    specialize (q (invmap (ϕo i) f) (invmap (ϕo i) g) (invmap (ϕo i) h)).
    repeat rewrite homotweqinvweq in q.
    apply q.
  - simpl. apply invweq.
    set (q:= pr2 (pr2 i)). simpl in q; clearbody q.
    specialize (q (invmap (ϕo i) f)).
    rewrite homotweqinvweq in q.
    apply q.
Qed.

Definition folds_iso_inv : folds_iso b a :=
  tpair _ folds_iso_inv_data folds_iso_inv_prop.

End folds_iso_inverse.

(** * Composition of FOLDS isomorphisms **)

Section folds_iso_comp.

Context {a b c : C} (i : folds_iso a b) (i' : folds_iso b c).

Definition folds_iso_comp_data : folds_iso_data a c.
Proof.
  repeat split.
  - intro x; apply (weqcomp (ϕ₁ i) (ϕ₁ i')).
  - intro z; apply (weqcomp (ϕ₂ i) (ϕ₂ i')).
  - apply (weqcomp (ϕo i) (ϕo i')).
Defined.

Lemma folds_iso_comp_prop : folds_iso_prop folds_iso_comp_data.
Proof.
  repeat split.
  - intros. simpl. eapply weqcomp.
    + apply (pr1 (pr1 (pr1 (pr1 (pr2 i))))). 
    + apply (pr1 (pr1 (pr1 (pr1 (pr2 i'))))).
  - intros; simpl; eapply weqcomp.
    + apply (pr2 (pr1 (pr1 (pr1 (pr2 i))))). 
    + apply (pr2 (pr1 (pr1 (pr1 (pr2 i'))))). 
  - intros; simpl; eapply weqcomp.
    + apply (pr2 (pr1 (pr1 (pr2 i)))). 
    + apply (pr2 (pr1 (pr1 (pr2 i')))). 
  - intros; simpl; eapply weqcomp.
    + apply (pr1 (pr1 (pr2 (pr1 (pr2 i))))). 
    + apply (pr1 (pr1 (pr2 (pr1 (pr2 i'))))).
  - intros; simpl; eapply weqcomp.
    + apply (pr2 (pr1 (pr2 (pr1 (pr2 i))))).
    + apply (pr2 (pr1 (pr2 (pr1 (pr2 i'))))).
  - intros; simpl; eapply weqcomp.
    + apply (pr1 (pr2 (pr2 (pr1 (pr2 i))))). 
    + apply (pr1 (pr2 (pr2 (pr1 (pr2 i'))))). 
  - intros; simpl; eapply weqcomp.
    + apply (pr2 (pr2 (pr2 (pr1 (pr2 i))))). 
    + apply (pr2 (pr2 (pr2 (pr1 (pr2 i'))))). 
  - intros; simpl; eapply weqcomp.
    + apply (pr2 (pr2 i)). 
    + apply (pr2 (pr2 i')). 
Qed.



End folds_iso_comp.

(** * From isomorphisms to FOLDS isomorphisms **)

Section from_iso_to_folds_iso.

Variables a b : C.
Variable f : iso (C:=C') a b.

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
      * transitivity (compose (compose (C:= C')  f0 (compose f (inv_from_iso f))) g).   
        rewrite iso_inv_after_iso. rewrite id_right. apply idpath.
        repeat rewrite assoc; apply idpath.
    + intro H. apply comp_compose2.
      set (H2 := comp_compose2' H). apply pathsinv0.
      etransitivity. 
      * apply (pathsinv0 H2).
      * transitivity (compose (compose (C:=C')  f0 (compose f (inv_from_iso f))) g).   
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
  (compose (compose (C:= C') f0 (compose (C:= C') f (inv_from_iso f)))(compose (C:= C') g  f)).
      * repeat rewrite assoc; apply idpath.
      * rewrite iso_inv_after_iso. rewrite id_right; apply assoc.
    + intro H; apply comp_compose2.
      set (H2 := comp_compose2' H).
      repeat rewrite assoc in H2.
      set (H3:= post_comp_with_iso_is_inj _  _ _ _ (pr2 f) _  _ _ H2). 
      rewrite <- H3; clear H3 H2 H.
      transitivity 
   (compose (compose (C:= C') f0 (compose (C:= C') f (inv_from_iso f))) g).
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
      set (H2:=pre_comp_with_iso_is_inj _ _ _  _ _ ((is_iso_inv_from_iso  _ _ f)) _ _ H); 
        clearbody H2; clear H.
      repeat rewrite  assoc in H2; rewrite assoc4 in H2.
      rewrite iso_inv_after_iso, id_right in H2.
      assumption.
  - simpl; apply logeqweq.
    + intro H; set (H':=comp_compose2' H); clearbody H'; clear H;
      rename H' into H; rewrite <- H; clear H.
      apply comp_compose2.
      repeat rewrite <- assoc; apply maponpaths; simpl.
      set (H':=assoc C' _ _ _ _ f0 g f); clearbody H';
      simpl in *. rewrite <- H'; clear H'.
      apply maponpaths. simpl in *. 
      repeat rewrite  (assoc C').
      rewrite iso_inv_after_iso, id_left; 
      apply idpath.
    + intro H; set (H':=comp_compose2' H); clearbody H'; clear H;
      rename H' into H.
      apply comp_compose2.
      repeat rewrite <- assoc in H.
      set (H':=pre_comp_with_iso_is_inj _ _ _  _ _ ((is_iso_inv_from_iso  _ _ f)) _ _ H); 
        clearbody H'; clear H.
      repeat rewrite assoc in H'.
      set (H'':=post_comp_with_iso_is_inj _ _ _ _ (pr2 f) _ _ _ H');
      clearbody H''; clear H'.
      rewrite assoc4, iso_inv_after_iso, id_right in H'';
      assumption.
  - simpl. apply logeqweq.  
    + intro H. apply id_identity2. 
      rewrite (id_identity2' H). rewrite (id_left C').
      apply (iso_after_iso_inv _ _ _ f).
    + intro H. apply id_identity2.
      set (H':=id_identity2' H); clearbody H'; clear H.
      set (H2:=iso_inv_to_left _ _ _ _ f _ _ H'); clearbody H2.
      rewrite id_right in H2.      
      transitivity (compose (C:= C') f (inv_from_iso f)).
      * apply (iso_inv_on_left C'); auto.
      * apply (iso_inv_after_iso C').
Qed.

Definition folds_iso_from_iso : folds_iso a b :=
  tpair _ _ folds_iso_data_prop.

End from_iso_to_folds_iso.

(** * from FOLDS isomorphism to isomorphism **)

Section from_folds_iso_to_iso.

Variables a b : C.
Variable i : folds_iso a b.

Let i': a ⇒ b := ϕ₁ i (identity (C:= C') _ ).
Let i'inv : b ⇒ a := ϕ₂ i (identity (C:= C') _ ).

Definition iso_from_folds_iso : iso (C:=C') a b.
Proof.
  exists i'.
  exists i'inv.
  apply ϕ₁_ϕ₂_are_inverse.
Defined.

End from_folds_iso_to_iso.

(** * from FOLDS isos to isos and back, and the other way round **)

Section iso_from_folds_from_iso.

Context {a b : C} (i : iso (C:=C') a b).

Lemma bla : iso_from_folds_iso _ _ (folds_iso_from_iso _ _ i) = i.
Proof.
  apply eq_iso.
  apply (id_left C').
Qed.


Variable i' : folds_iso a b.

Lemma bla2 : folds_iso_from_iso _ _ (iso_from_folds_iso _ _ i') = i'.
Proof.
  apply folds_iso_equal.
  apply (id_left C').
Qed.
 

End iso_from_folds_from_iso.




End folds_iso_def.


