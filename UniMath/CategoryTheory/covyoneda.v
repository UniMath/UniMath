
(** **********************************************************

Benedikt Ahrens, Anders Mörtberg (adapted from yoneda.v)

2016


************************************************************)


(** **********************************************************

Contents : Definition of the covariant Yoneda functor
           [covyoneda(C) : [C^op, [C, HSET]]]

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.

Ltac unf := unfold identity,
                   compose,
                   precategory_morphisms;
                   simpl.

(** The following lemma is already in precategories.v . It should be transparent? *)

(* Lemma iso_comp_left_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) : *)
(*   isweq (λ f : hom _ c a, f · h). *)
(* Proof. intros. apply (@iso_comp_right_isweq C^op b a (opp_iso h)). Qed. *)

(** * Covariant Yoneda functor *)

(** ** On objects *)

Definition covyoneda_objects_ob (C : precategory) (c : C^op)
          (d : C) := C⟦c,d⟧.

(* Definition covyoneda_objects_mor (C : precategory) (c : C^op) *)
(*     (d d' : C) (f : C⟦d,d'⟧) : *)
(*    covyoneda_objects_ob C c d -> covyoneda_objects_ob C c d' := *)
(*     λ g, g · f. *)

Definition covyoneda_ob_functor_data (C : precategory) (hs : has_homsets C) (c : C^op) :
    functor_data C HSET.
Proof.
exists (λ c', hSetpair (covyoneda_objects_ob C c c') (hs c c')) .
intros a b f g. unfold covyoneda_objects_ob in *. simpl in *.
exact (g · f).
Defined.

Lemma is_functor_covyoneda_functor_data (C : precategory) (hs: has_homsets C) (c : C^op) :
  is_functor (covyoneda_ob_functor_data C hs c).
Proof.
split.
- intros c'; apply funextfun; intro x; apply id_right.
- intros a b d f g; apply funextfun; intro h; apply assoc.
Qed.

Definition covyoneda_objects (C : precategory) (hs: has_homsets C) (c : C^op) :
             functor C HSET :=
    tpair _ _ (is_functor_covyoneda_functor_data C hs c).

(** ** On morphisms *)

Definition covyoneda_morphisms_data (C : precategory) (hs: has_homsets C) (c c' : C^op)
    (f : C^op⟦c,c'⟧) : ∏ a : C,
         HSET⟦covyoneda_objects C hs c a,covyoneda_objects C hs c' a⟧.
Proof.
simpl in f; intros a g.
apply (f · g).
Defined.

Lemma is_nat_trans_covyoneda_morphisms_data (C : precategory) (hs: has_homsets C)
     (c c' : C^op) (f : C^op⟦c,c'⟧) :
  is_nat_trans (covyoneda_objects C hs c) (covyoneda_objects C hs c')
               (covyoneda_morphisms_data C hs c c' f).
Proof.
intros d d' g; apply funextsec; intro h; apply assoc.
Qed.

Definition covyoneda_morphisms (C : precategory) (hs: has_homsets C) (c c' : C^op)
   (f : C^op⟦c,c'⟧) : nat_trans (covyoneda_objects C hs c) (covyoneda_objects C hs c') :=
   tpair _ _ (is_nat_trans_covyoneda_morphisms_data C hs c c' f).

Definition covyoneda_functor_data (C : precategory) (hs : has_homsets C) :
   functor_data C^op [C,HSET,has_homsets_HSET] :=
   tpair _ (covyoneda_objects C hs) (covyoneda_morphisms C hs).

(** ** Functorial properties of the yoneda assignments *)

Lemma is_functor_covyoneda (C : precategory) (hs: has_homsets C):
  is_functor (covyoneda_functor_data C hs).
Proof.
split.
- intro a.
  apply (@nat_trans_eq C _ has_homsets_HSET).
  intro c; apply funextsec; intro f; simpl in *.
  apply id_left.
- intros a b c f g.
  apply (@nat_trans_eq C _ has_homsets_HSET).
  simpl; intro d; apply funextsec; intro h; apply pathsinv0, assoc.
Qed.

Definition covyoneda (C : precategory) (hs: has_homsets C) :
  functor C^op [C, HSET, has_homsets_HSET] :=
   tpair _ _ (is_functor_covyoneda C hs).


(** TODO: adapt the rest? *)

(* (* Notation "'ob' F" := (precategory_ob_mor_fun_objects F)(at level 4). *) *)

(* (** ** Yoneda lemma: natural transformations from [yoneda C c] to [F] *)
(*          are isomorphic to [F c] *) *)


(* Definition yoneda_map_1 (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) : *)
(*        hom _ (yoneda C hs c) F -> pr1 (F c) := *)
(*    λ h,  pr1 h c (identity c). *)



(* Lemma yoneda_map_2_ax (C : precategory) (hs: has_homsets C) (c : C) *)
(*        (F : functor C^op HSET) (x : pr1 (F c)) : *)
(*   is_nat_trans (pr1 (yoneda C hs c)) F *)
(*          (fun (d : C) (f : hom (C ^op) c d) => #F f x). *)
(* Proof. *)
(*   intros a b f; simpl in *. *)
(*   apply funextsec. *)
(*   unfold yoneda_objects_ob; intro g. *)
(*   set (H:= functor_comp F  _ _  b g). *)
(*   unfold functor_comp in H; *)
(*   unfold opp_precat_data in H; *)
(*   simpl in *. *)
(*   apply (toforallpaths _ _ _ (H f) x). *)
(* Qed. *)

(* Definition yoneda_map_2 (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) : *)
(*        pr1 (F c) -> hom _ (yoneda C hs c) F. *)
(* Proof. *)
(*   intro x. *)
(*   exists (λ d : ob C, λ f, #F f x). *)
(*   apply yoneda_map_2_ax. *)
(* Defined. *)

(* Lemma yoneda_map_1_2 (C : precategory) (hs: has_homsets C) (c : C) *)
(*   (F : functor C^op HSET) *)
(*   (alpha : hom _ (yoneda C hs c) F) : *)
(*       yoneda_map_2 _ _ _ _ (yoneda_map_1 _ _ _ _ alpha) = alpha. *)
(* Proof. *)
(*   simpl in *. *)
(*   set (T:=nat_trans_eq (C:=C^op) (has_homsets_HSET)). *)
(*   apply T. *)
(*   intro a'; simpl. *)
(*   apply funextsec; intro f. *)
(*   unfold yoneda_map_1. *)
(*   pathvia ((alpha c · #F f) (identity c)). *)
(*     apply idpath. *)
(*   rewrite <- nat_trans_ax. *)
(*   unf; apply maponpaths. *)
(*   apply (id_right C a' c f ). *)
(* Qed. *)


(* Lemma yoneda_map_2_1 (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) (x : pr1 (F c)) : *)
(*    yoneda_map_1 _ _ _ _ (yoneda_map_2 _ hs  _ _ x) = x. *)
(* Proof. *)
(*   simpl. *)
(*   rewrite (functor_id F). *)
(*   apply idpath. *)
(* Qed. *)

(* Lemma isaset_nat_trans_yoneda (C: precategory) (hs: has_homsets C) (c : C) *)
(*   (F : functor C^op HSET) : *)
(*  isaset (nat_trans (yoneda_ob_functor_data C hs c) F). *)
(* Proof. *)
(*   apply isaset_nat_trans. *)
(*   apply (has_homsets_HSET). *)
(* Qed. *)



(* Lemma yoneda_iso_sets (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) : *)
(*    is_iso (C:=HSET) *)
(*      (a := hSetpair (hom _ ((yoneda C) hs c) F) (isaset_nat_trans_yoneda C hs c F)) *)
(*      (b := F c) *)
(*      (yoneda_map_1 C hs c F). *)
(* Proof. *)
(*   set (T:=yoneda_map_2 C hs c F). simpl in T. *)
(*   set (T':= T : hom HSET (F c) (hSetpair (hom _ ((yoneda C) hs c) F) *)
(*                                          (isaset_nat_trans_yoneda C hs c F))). *)
(*   apply (is_iso_qinv (C:=HSET) _ T' ). *)
(*   repeat split; simpl. *)
(*   - apply funextsec; intro alpha. *)
(*     unf; simpl. *)
(*     apply (yoneda_map_1_2 C hs c F). *)
(*   - apply funextsec; intro x. *)
(*     unf; rewrite (functor_id F). *)
(*     apply idpath. *)
(* Defined. *)



(* Definition yoneda_iso_target (C : precategory) (hs : has_homsets C) *)
(*            (F : [C^op, HSET, has_homsets_HSET]) *)
(*   : functor C^op HSET. *)
(* Proof. *)
(*   simple refine (@functor_composite _ [C^op, HSET, has_homsets_HSET]^op _ _ _  ). *)
(*   - apply functor_opp. *)
(*     apply yoneda. apply hs. *)
(*   - apply (yoneda _ (functor_category_has_homsets _ _ _ ) F). *)
(* Defined. *)

(* Lemma is_natural_yoneda_iso (C : precategory) (hs : has_homsets C) (F : functor C^op HSET): *)
(*   is_nat_trans (yoneda_iso_target C hs F) F *)
(*   (λ c, yoneda_map_1 C hs c F). *)
(* Proof. *)
(*   unfold is_nat_trans. *)
(*   intros c c' f. cbn in *. *)
(*   apply funextsec. *)
(*   unfold yoneda_ob_functor_data. cbn. *)
(*   unfold yoneda_morphisms_data. *)
(*   unfold yoneda_map_1. *)
(*   intro X. *)
(*   assert (XH := nat_trans_ax X). *)
(*   cbn in XH. unfold yoneda_objects_ob in XH. *)
(*   assert (XH' := XH c' c' (identity _ )). *)
(*   assert (XH2 := toforallpaths _ _ _ XH'). *)
(*   rewrite XH2. *)
(*   rewrite (functor_id F). *)
(*   cbn. *)
(*   clear XH2 XH'. *)
(*   assert (XH' := XH _ _ f). *)
(*   assert (XH2 := toforallpaths _ _ _ XH'). *)
(*   eapply pathscomp0. Focus 2. apply XH2. *)
(*   rewrite id_right. *)
(*   apply idpath. *)
(* Qed. *)

(* Definition natural_trans_yoneda_iso (C : precategory) (hs : has_homsets C) *)
(*   (F : functor C^op HSET) *)
(*   : nat_trans (yoneda_iso_target C hs F) F *)
(*   := tpair _ _ (is_natural_yoneda_iso C hs F). *)



(* Lemma is_natural_yoneda_iso_inv (C : precategory) (hs : has_homsets C) (F : functor C^op HSET): *)
(*   is_nat_trans F (yoneda_iso_target C hs F) *)
(*   (λ c, yoneda_map_2 C hs c F). *)
(* Proof. *)
(*   unfold is_nat_trans. *)
(*   intros c c' f. cbn in *. *)
(*   apply funextsec. *)
(*   unfold yoneda_ob_functor_data. cbn. *)
(*   unfold yoneda_map_2. *)
(*   intro A. *)
(*   apply nat_trans_eq. { apply (has_homsets_HSET). } *)
(*   cbn. intro d. *)
(*   apply funextfun. *)
(*   unfold yoneda_objects_ob. intro g. *)
(*   unfold yoneda_morphisms_data. *)
(*   apply (! toforallpaths _ _ _ (functor_comp F _ _ _ _ _ ) A). *)
(* Qed. *)

(* Definition natural_trans_yoneda_iso_inv (C : precategory) (hs : has_homsets C) *)
(*   (F : functor C^op HSET) *)
(*   : nat_trans (yoneda_iso_target C hs F) F *)
(*   := tpair _ _ (is_natural_yoneda_iso C hs F). *)


(* Lemma isweq_yoneda_map_1 (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) : *)
(*   isweq *)
(*      (*a := hSetpair (hom _ ((yoneda C) hs c) F) (isaset_nat_trans_yoneda C hs c F)*) *)
(*      (*b := F c*) *)
(*      (yoneda_map_1 C hs c F). *)
(* Proof. *)
(*   set (T:=yoneda_map_2 C hs c F). simpl in T. *)
(*   simple refine (gradth _ _ _ _ ). *)
(*   - apply T. *)
(*   - apply yoneda_map_1_2. *)
(*   - apply yoneda_map_2_1. *)
(* Defined. *)

(* Definition yoneda_weq (C : precategory) (hs: has_homsets C) (c : C) *)
(*    (F : functor C^op HSET) *)
(*   :  hom [C^op, HSET, has_homsets_HSET] ((yoneda C hs) c) F ≃ pr1hSet (F c) *)
(*   := weqpair _ (isweq_yoneda_map_1 C hs c F). *)


(* (** ** The Yoneda embedding is fully faithful *) *)

(* Lemma yoneda_fully_faithful (C : precategory) (hs: has_homsets C) : fully_faithful (yoneda C hs). *)
(* Proof. *)
(*   intros a b; simpl. *)
(*   apply (gradth _ *)
(*       (yoneda_map_1 C hs a (pr1 (yoneda C hs) b))). *)
(*   - intro; simpl in *. *)
(*     apply id_left. *)
(*   - intro gamma. *)
(*     simpl in *. *)
(*     apply nat_trans_eq. apply (has_homsets_HSET). *)
(*     intro x. simpl in *. *)
(*     apply funextsec; intro f. *)
(*     unfold yoneda_map_1. *)
(*     unfold yoneda_morphisms_data. *)
(*     assert (T:= toforallpaths _ _ _ (nat_trans_ax gamma a x f) (identity _ )). *)
(*     cbn in T. *)
(*     eapply pathscomp0; [apply (!T) |]. *)
(*     apply maponpaths. *)
(*     apply id_right. *)
(* Defined. *)


(* Section yoneda_functor_precomp. *)

(* Variables C D : precategory. *)
(* Variables (hsC : has_homsets C) (hsD : has_homsets D). *)
(* Variable F : functor C D. *)

(* Section fix_object. *)

(* Variable c : C. *)

(* Definition yoneda_functor_precomp' : nat_trans (yoneda_objects C hsC c) *)
(*       (functor_composite (functor_opp F) (yoneda_objects D hsD (F c))). *)
(* Proof. *)
(*   simple refine (tpair _ _ _ ). *)
(*   - intros d f ; simpl. *)
(*     apply (#F f). *)
(*   - abstract (intros d d' f ; *)
(*               apply funextsec; intro t; simpl; *)
(*               apply functor_comp). *)
(* Defined. *)

(* Definition yoneda_functor_precomp :  _ ⟦ yoneda C hsC c, functor_composite (functor_opp F) (yoneda_objects D hsD (F c))⟧. *)
(* Proof. *)
(*   exact yoneda_functor_precomp'. *)
(* Defined. *)

(* Variable Fff : fully_faithful F. *)

(* Lemma is_iso_yoneda_functor_precomp : is_iso yoneda_functor_precomp. *)
(* Proof. *)
(*   apply functor_iso_if_pointwise_iso. *)
(*   intro. simpl. *)
(*   set (T:= weqpair _ (Fff a c)). *)
(*   set (TA := hSetpair (hom C a c) (hsC _ _ )). *)
(*   set (TB := hSetpair (hom D (F a) (F c)) (hsD _ _ )). *)
(*   apply (hset_equiv_is_iso TA TB T). *)
(* Defined. *)

(* End fix_object. *)


(* Let A := functor_composite F (yoneda D hsD). *)
(* Let B := pre_composition_functor _ _ HSET (has_homsets_opp hsD) (has_homsets_HSET)  (functor_opp F). *)

(* Definition yoneda_functor_precomp_nat_trans : *)
(*     @nat_trans *)
(*       C *)
(*       [C^op, HSET, (has_homsets_HSET)] *)
(*       (yoneda C hsC) *)
(*       (functor_composite A B). *)
(* Proof. *)
(*   simple refine (tpair _ _ _ ). *)
(*   - intro c; simpl. *)
(*     apply yoneda_functor_precomp. *)
(*   - abstract ( *)
(*         intros c c' f; *)
(*         apply nat_trans_eq; try apply (has_homsets_HSET); *)
(*         intro d; apply funextsec; intro t; *)
(*         cbn; *)
(*         apply functor_comp). *)
(* Defined. *)

(* End yoneda_functor_precomp. *)
