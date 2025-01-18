
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

Require Export UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Functors.
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

Definition covyoneda_objects_ob (C : category) (c : C^op)
          (d : C) := C⟦c,d⟧.

(* Definition covyoneda_objects_mor (C : precategory) (c : C^op) *)
(*     (d d' : C) (f : C⟦d,d'⟧) : *)
(*    covyoneda_objects_ob C c d -> covyoneda_objects_ob C c d' := *)
(*     λ g, g · f. *)

Definition covyoneda_ob_functor_data (C : category) (c : C^op) :
    functor_data C HSET.
Proof.
exists (λ c', make_hSet (covyoneda_objects_ob C c c') (homset_property C c c')) .
intros a b f g. unfold covyoneda_objects_ob in *. simpl in *.
exact (g · f).
Defined.

Lemma is_functor_covyoneda_functor_data (C : category) (c : C^op) :
  is_functor (covyoneda_ob_functor_data C c).
Proof.
split.
- intros c'; apply funextfun; intro x; apply id_right.
- intros a b d f g; apply funextfun; intro h; apply assoc.
Qed.

Definition covyoneda_objects (C : category) (c : C^op) :
             functor C HSET :=
    tpair _ _ (is_functor_covyoneda_functor_data C c).

(** ** On morphisms *)

Definition covyoneda_morphisms_data (C : category) (c c' : C^op)
    (f : C^op⟦c,c'⟧) : ∏ a : C,
         HSET⟦covyoneda_objects C  c a,covyoneda_objects C  c' a⟧.
Proof.
simpl in f; intros a g.
apply (f · g).
Defined.

Lemma is_nat_trans_covyoneda_morphisms_data (C : category)
     (c c' : C^op) (f : C^op⟦c,c'⟧) :
  is_nat_trans (covyoneda_objects C c) (covyoneda_objects C c')
               (covyoneda_morphisms_data C c c' f).
Proof.
intros d d' g; apply funextsec; intro h; apply assoc.
Qed.

Definition covyoneda_morphisms (C : category) (c c' : C^op)
   (f : C^op⟦c,c'⟧) : nat_trans (covyoneda_objects C c) (covyoneda_objects C c') :=
   tpair _ _ (is_nat_trans_covyoneda_morphisms_data C c c' f).

Definition covyoneda_functor_data (C : category) :
   functor_data C^op [C,HSET,has_homsets_HSET] :=
   tpair _ (covyoneda_objects C) (covyoneda_morphisms C).

(** ** Functorial properties of the yoneda assignments *)

Lemma is_functor_covyoneda (C : category) :
  is_functor (covyoneda_functor_data C).
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

Definition covyoneda (C : category) :
  functor C^op [C, HSET, has_homsets_HSET] :=
   tpair _ _ (is_functor_covyoneda C).


(** TODO: adapt the rest? *)


(* Notation "'ob' F" := (precategory_ob_mor_fun_objects F)(at level 4). *)

(** ** covyoneda lemma: natural transformations from [covyoneda C c] to [F]
         are isomorphic to [F c] *)


Definition covyoneda_map_1 (C : category) (c : C)
   (F : functor C HSET) :
      [C, SET]⟦covyoneda C c, F⟧ -> pr1 (F c) :=
   λ h,  pr1 h c (identity c).

Lemma covyoneda_map_2_ax (C : category) (c : C)
       (F : functor C HSET) (x : pr1 (F c)) :
  is_nat_trans (pr1 (covyoneda C c)) F
         (fun (d : C) (f : C⟦c, d⟧) => #F f x).
Proof.
  intros a b f; simpl in *.
  apply funextsec.
  unfold covyoneda_objects_ob; intro g.
  set (H:= @functor_comp _ _ F  _ _  b g).
  unfold functor_comp in H;
  unfold opp_precat_data in H;
  simpl in *.
  apply (toforallpaths _ _ _ (H f) x).
Qed.

Definition covyoneda_map_2 (C : category) (c : C)
   (F : functor C HSET) :
       pr1 (F c) -> [C, SET]⟦covyoneda C c, F⟧.
Proof.
  intro x.
  exists (λ d : ob C, λ f, #F f x).
  apply covyoneda_map_2_ax.
Defined.

Lemma covyoneda_map_1_2 (C : category) (c : C)
  (F : functor C HSET)
  (alpha : [C, SET]⟦covyoneda C c, F⟧) :
      covyoneda_map_2 _ _ _ (covyoneda_map_1 _ _ _ alpha) = alpha.
Proof.
  simpl in *.
  apply (nat_trans_eq (has_homsets_HSET)).
  intro a'; simpl.
  apply funextsec; intro f.
  unfold covyoneda_map_1.
  intermediate_path ((alpha c · #F f) (identity c)).
    apply idpath.
  rewrite <- nat_trans_ax.
  unf; apply maponpaths.
  apply (id_left f ).
Qed.

Lemma covyoneda_map_2_1 (C : category) (c : C)
   (F : functor C HSET) (x : pr1 (F c)) :
   covyoneda_map_1 _ _ _ (covyoneda_map_2 _  _ _ x) = x.
Proof.
  simpl.
  rewrite (functor_id F).
  apply idpath.
Qed.

Lemma isaset_nat_trans_covyoneda (C: category) (c : C)
  (F : functor C HSET) :
 isaset (nat_trans (covyoneda_ob_functor_data C c) F).
Proof.
  apply isaset_nat_trans.
  apply (has_homsets_HSET).
Qed.

Lemma covyoneda_iso_sets (C : category) (c : C)
   (F : functor C HSET) :
   is_z_isomorphism (C:=HSET)
     (a := make_hSet _ (isaset_nat_trans_covyoneda C c F))
     (covyoneda_map_1 C c F).
Proof.
  set (T:= covyoneda_map_2 C c F).
  exists T.
  split; simpl.
  - apply funextsec; intro alpha.
    unf; simpl.
    apply (covyoneda_map_1_2 C c F).
  - apply funextsec; intro x.
    unf; rewrite (functor_id F).
    apply idpath.
Defined.

Lemma isweq_covyoneda_map_1
  (C : category)
  (c : C)
  (F : functor C HSET)
  : isweq (covyoneda_map_1 C c F).
Proof.
  use isweq_iso.
  - apply (covyoneda_map_2 C c F).
  - apply covyoneda_map_1_2.
  - apply covyoneda_map_2_1.
Defined.

Definition covyoneda_weq (C : category) (c : C)
   (F : functor C HSET)
  : [C, HSET]⟦covyoneda C c, F⟧ ≃ pr1hSet (F c)
  := make_weq _ (isweq_covyoneda_map_1 C c F).


(** ** The covyoneda embedding is fully faithful *)

Lemma covyoneda_fully_faithful (C : category) : fully_faithful (covyoneda C).
Proof.
  intros a b; simpl.
  apply (isweq_iso _
      (covyoneda_map_1 C a (pr1 (covyoneda C) b))).
  - intro; simpl in *.
    apply id_right.
  - intro gamma.
    simpl in *.
    apply nat_trans_eq. apply (has_homsets_HSET).
    intro x. simpl in *.
    apply funextsec; intro f.
    unfold covyoneda_map_1.
    unfold covyoneda_morphisms_data.
    assert (T:= toforallpaths _ _ _ (nat_trans_ax gamma a x f) (identity _ )).
    cbn in T.
    eapply pathscomp0; [apply (!T) |].
    apply maponpaths.
    apply id_left.
Defined.
