
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of opposite category
 	
	   Definition of the Yoneda functor 
           [yoneda(C) : [C, [C^op, HSET]]]
	
           Proof that [yoneda(C)] is fully faithful  
           
************************************************************)


Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.functors_transformations.

(*Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).*)
Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).
Local Notation "f ;; g" := (compose f g)(at level 50).
Local Notation "[ C , D ]" := (functor_precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "x ,, y" := (tpair _ x y) (at level 69, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


(** * The opposite precategory of a precategory *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> UU) (ob C) 
        (fun a b : ob C => hom C b a ).

Definition opp_precat_data (C : precategory_data) : precategory_data.
Proof.
  exists (opp_precat_ob_mor C).
  intros a b c f g.
  exact (g ;; f).
Defined.

Hint Unfold identity.

Ltac unf := unfold identity, 
                   compose, 
                   precategory_morphisms;
                   simpl.

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
  repeat split; simpl.
  - exists (fun a => identity a).
    repeat split;
    intros; unf;
    try apply id_right; try apply id_left.
  - intros; unf; apply pathsinv0, assoc.
Defined.

Definition opp_precat (C : precategory) : precategory := 
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Local Notation "C '^op'" := (opp_precat C) (at level 3).

Definition opp_iso {C:precategory} {a b:ob C} : @iso C a b -> @iso C^op b a.
  intro f.
  exists (pr1 f).
  set (T:= is_z_iso_from_is_iso _ (pr2 f)).
  apply (is_iso_qinv (C:=C^op) _ (pr1 T)).
  split. 
  - apply (pr2 (pr2 T)).
  - apply (pr1 (pr2 T)).
Defined.

(** The following lemma is already in precategories.v . It should be transparent? *)

Lemma iso_comp_left_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : hom _ c a => f ;; h).
Proof. intros. apply (@iso_comp_right_isweq C^op b a (opp_iso h)). Qed.

(** * Yoneda functor *)

(** ** On objects *)

Definition yoneda_objects_ob (C : precategory) (c : C)
          (d : C) := hom C d c.

Definition yoneda_objects_mor (C : precategory) (c : C)
    (d d' : C) (f : hom C d  d') :
   yoneda_objects_ob C c d' -> yoneda_objects_ob C c d :=
    fun g => f ;; g.

Definition yoneda_ob_functor_data (C : precategory) (hs: has_homsets C) (c : C) :
    functor_data (C^op) HSET.
Proof.
  exists (fun c' => hSetpair (yoneda_objects_ob C c c') (hs c' c)) .
  intros a b f g. unfold yoneda_objects_ob in *. simpl in *.
  exact (f ;; g).
Defined.


Lemma is_functor_yoneda_functor_data (C : precategory) (hs: has_homsets C) (c : C) :
  is_functor (yoneda_ob_functor_data C hs c).
Proof.
  repeat split; unf; simpl.
  intros.
  apply funextsec.
  intro f. unf. apply id_left.
  intros a b d f g.
  apply funextsec. intro h.
  apply (! assoc _ _ _ _ _ _ _ _ ).
Qed.

Definition yoneda_objects (C : precategory) (hs: has_homsets C) (c : C) : 
             functor C^op HSET :=
    tpair _ _ (is_functor_yoneda_functor_data C hs c).


(** ** On morphisms *)

Definition yoneda_morphisms_data (C : precategory)(hs: has_homsets C) (c c' : C) 
    (f : hom C c c') : forall a : ob C^op, 
         hom _ (yoneda_objects C hs c a) ( yoneda_objects C hs c' a) := 
            fun a g => g ;; f.

Lemma is_nat_trans_yoneda_morphisms_data (C : precategory) (hs: has_homsets C)
     (c c' : ob C) (f : hom C c c') :
  is_nat_trans (yoneda_objects C hs c) (yoneda_objects C hs c') 
    (yoneda_morphisms_data C hs c c' f).
Proof.
  unfold is_nat_trans; simpl. 
  unfold yoneda_morphisms_data; simpl.
  intros d d' g.
  apply funextsec; simpl in *.
  unfold yoneda_objects_ob; simpl.
  unf; intro; 
  apply  ( ! assoc _ _ _ _ _ _ _ _  ).
Qed.

Definition yoneda_morphisms (C : precategory) (hs: has_homsets C) (c c' : C)
   (f : hom C c c') : nat_trans (yoneda_objects C hs c) (yoneda_objects C hs c') :=
   tpair _ _ (is_nat_trans_yoneda_morphisms_data C hs c c' f).


Definition yoneda_functor_data (C : precategory)(hs: has_homsets C) : 
   functor_data C [C^op , HSET, (pr2 is_category_HSET) ] := 
   tpair _ (yoneda_objects C hs) (yoneda_morphisms C hs).


(** ** Functorial properties of the yoneda assignments *)

Lemma is_functor_yoneda (C : precategory) (hs: has_homsets C):
  is_functor (yoneda_functor_data C hs).
Proof.
  unfold is_functor.
  repeat split; simpl.
  intro a. 
  set (T:= nat_trans_eq (C:=C^op) (pr2 is_category_HSET)). simpl.
  apply T.
  intro c; apply funextsec; intro f.
  apply id_right.
  intros a b c f g.
  set (T:=nat_trans_eq (C:=C^op) (pr2 is_category_HSET)).
  apply T. 
  simpl; intro d; apply funextsec; intro h.
  apply assoc.
Qed.


Definition yoneda (C : precategory) (hs: has_homsets C) : 
  functor C [C^op, HSET, (pr2 is_category_HSET)] :=
   tpair _ _ (is_functor_yoneda C hs).

(* Notation "'ob' F" := (precategory_ob_mor_fun_objects F)(at level 4). *)

(** ** Yoneda lemma: natural transformations from [yoneda C c] to [F]
         are isomorphic to [F c] *)


Definition yoneda_map_1 (C : precategory) (hs: has_homsets C) (c : C)
   (F : functor C^op HSET) :
       hom _ (yoneda C hs c) F -> pr1 (F c) := 
   fun h =>  pr1 h c (identity c).



Lemma yoneda_map_2_ax (C : precategory) (hs: has_homsets C) (c : C)
       (F : functor C^op HSET) (x : pr1 (F c)) :
  is_nat_trans (pr1 (yoneda C hs c)) F 
         (fun (d : C) (f : hom (C ^op) c d) => #F f x).
Proof.
  intros a b f; simpl in *.
  apply funextsec.
  unfold yoneda_objects_ob; intro g.
  set (H:= functor_comp F  _ _  b g).
  unfold functor_comp in H;
  unfold opp_precat_data in H;
  simpl in *.
  apply (toforallpaths _ _ _ (H f) x).
Qed.

Definition yoneda_map_2 (C : precategory) (hs: has_homsets C) (c : C)
   (F : functor C^op HSET) :
       pr1 (F c) -> hom _ (yoneda C hs c) F.
Proof.
  intro x.
  exists (fun d : ob C => fun f => #F f x).
  apply yoneda_map_2_ax.
Defined.

Lemma yoneda_map_1_2 (C : precategory) (hs: has_homsets C) (c : C)
  (F : functor C^op HSET)
  (alpha : hom _ (yoneda C hs c) F) :
      yoneda_map_2 _ _ _ _ (yoneda_map_1 _ _ _ _ alpha) = alpha.
Proof.
  simpl in *. 
  set (T:=nat_trans_eq (C:=C^op) (pr2 is_category_HSET)).
  apply T.
  intro a'; simpl.
  apply funextsec; intro f.
  unfold yoneda_map_1.
  pathvia ((alpha c ;; #F f) (identity c)).
    apply idpath.
  rewrite <- nat_trans_ax.
  unf; apply maponpaths.
  apply (id_right C a' c f ).
Qed.


Lemma yoneda_map_2_1 (C : precategory) (hs: has_homsets C) (c : C)
   (F : functor C^op HSET) (x : pr1 (F c)) : 
   yoneda_map_1 _ _ _ _ (yoneda_map_2 _ hs  _ _ x) = x.
Proof.
  simpl.
  rewrite (functor_id F).
  apply idpath.
Qed.

Lemma isaset_nat_trans_yoneda (C: precategory) (hs: has_homsets C) (c : C) 
  (F : functor C^op HSET) :
 isaset (nat_trans (yoneda_ob_functor_data C hs c) F).
Proof.
  apply isaset_nat_trans.
  apply (pr2 is_category_HSET).
Qed.



Lemma yoneda_iso_sets (C : precategory) (hs: has_homsets C) (c : C)
   (F : functor C^op HSET) : 
   is_isomorphism (C:=HSET) 
     (a := hSetpair (hom _ ((yoneda C) hs c) F) (isaset_nat_trans_yoneda C hs c F))
     (b := F c)
     (yoneda_map_1 C hs c F).
Proof.
  set (T:=yoneda_map_2 C hs c F). simpl in T.
  set (T':= T : hom HSET (F c) (hSetpair (hom _ ((yoneda C) hs c) F) 
                                         (isaset_nat_trans_yoneda C hs c F))).
  apply (is_iso_qinv (C:=HSET) _ T' ).
  repeat split; simpl.
  - apply funextsec; intro alpha.
    unf; simpl.
    apply (yoneda_map_1_2 C hs c F).
  - apply funextsec; intro x.
    unf; rewrite (functor_id F).
    apply idpath.
Defined.


(** ** The Yoneda embedding is fully faithful *)

Lemma yoneda_fully_faithful (C : precategory) (hs: has_homsets C) : fully_faithful (yoneda C hs).
Proof.
  intros a b; simpl.
  assert (eximio : yoneda_morphisms C hs a b = yoneda_map_2 C hs a (yoneda C hs b)).
  - apply funextsec; intro f.
    apply nat_trans_eq; intro c; simpl.
    apply (pr2 is_category_HSET).
    apply funextsec; intro g.
    apply idpath.
  - rewrite eximio.
    apply (gradth _ 
      (yoneda_map_1 C hs a (pr1 (yoneda C hs) b))).
    intro; apply yoneda_map_2_1.
    intro; apply yoneda_map_1_2.
Qed.


















