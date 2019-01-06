(** ** Full sub(pre)categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)
Reorganized: Langston Barrett (@siddharthist) (March 2018)

*)

(** ** Contents

    Image of a functor, full subcat specified by a functor

    The inclusion of a full subcategory is fully faithful
      Fullness
      Faithfulness

    Subcategories, back to
      Inclusion functor
      Full image of a functor
      Factorization of a functor via its
          full image
      This factorization is fully faithful
          if the functor is
          [functor_full_img_fully_faithful_if_fun_is]

      Isos in full subcategory are equiv
        to isos in the precategory

      Full subcategory of a univalent_category is
        a univalent_category
        [is_univalent_full_subcat]

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Local Open Scope cat.

(** A full subcategory has the true predicate on morphisms *)

Lemma is_sub_precategory_full (C : precategory)
         (C':hsubtype (ob C)) : is_sub_precategory C' (λ a b, λ f, htrue).
Proof.
  split;
  intros; exact tt.
Defined.

Definition full_sub_precategory {C : precategory}
         (C': hsubtype (ob C)) :
   sub_precategories C :=
  tpair _  (dirprodpair C' (λ a b f, htrue)) (is_sub_precategory_full C C').

(** Any morphism between appropriate objects is a morphism of the full subprecategory *)
Definition morphism_in_full_subcat {C : precategory} {C' : hsubtype (ob C)}
   {a b : ob (full_sub_precategory C')} (f : pr1 a --> pr1 b) :
    precategory_morphisms a b := precategory_morphisms_in_subcat f tt.

(** ** The inclusion of a full subcategory is fully faithful *)

Section FullyFaithful.
  Context (C : precategory) (C' : hsubtype (ob C)).

  (** *** Fullness *)

  Lemma full_sub_precategory_inclusion :
    full (sub_precategory_inclusion C (full_sub_precategory C')).
  Proof.
    intros a b f.
    apply hinhpr.
    unfold hfiber.
    exists (f,, tt).
    reflexivity.
  Qed.

  (** *** Faithfulness *)

  Lemma faithful_sub_precategory_inclusion :
    faithful (sub_precategory_inclusion C (full_sub_precategory C')).
  Proof.
    intros a b; cbn.
    apply isinclpr1.
    intro; apply isapropunit.
  Qed.

  Lemma fully_faithful_sub_precategory_inclusion :
    fully_faithful (sub_precategory_inclusion C (full_sub_precategory C')).
  Proof.
    apply full_and_faithful_implies_fully_faithful.
    split.
    - apply full_sub_precategory_inclusion.
    - apply faithful_sub_precategory_inclusion.
  Qed.

End FullyFaithful.

(** ** The (full) image of a functor *)

Definition full_img_sub_precategory {C D : precategory}(F : functor C D) :
    sub_precategories D :=
       full_sub_precategory (sub_img_functor F).

(** ** Given a functor F : C -> D, we obtain a functor F : C -> Img(F) *)

Definition full_img_functor_obj {C D : precategory}(F : functor C D) :
   ob C -> ob (full_img_sub_precategory F).
Proof.
  intro c.
  exists (F c).
  intros a b.
  apply b.
  exists c.
  apply identity_iso.
Defined.

Definition full_img_functor_data {C D : precategory}(F : functor C D) :
  functor_data C (full_img_sub_precategory F).
Proof.
  exists (full_img_functor_obj F).
  intros a b f.
  exists (#F f).
  exact tt.
Defined.

Lemma is_functor_full_img (C D: precategory) (F : functor C D) :
  is_functor (full_img_functor_data F).
Proof.
  split.
  intro a; simpl.
  apply subtypeEquality.
    intro; apply pr2.
  apply functor_id.
  intros a b c f g.
  set ( H := eq_in_sub_precategory D (full_img_sub_precategory F)).
  apply (H (full_img_functor_obj F a)(full_img_functor_obj F c)).
  simpl; apply functor_comp.
Qed.

Definition functor_full_img {C D: precategory}
       (F : functor C D) :
   functor C (full_img_sub_precategory F) :=
   tpair _ _ (is_functor_full_img C D F).


(** *** Morphisms in the full subprecat are equiv to morphisms in the precategory *)
(** does of course not need the univalent_category hypothesis *)

Definition hom_in_subcat_from_hom_in_precat (C : precategory)
 (C' : hsubtype (ob C))
  (a b : ob (full_sub_precategory C'))
      (f : pr1 a --> pr1 b) : a --> b :=
       tpair _ f tt.

Definition hom_in_precat_from_hom_in_full_subcat (C : precategory)
 (C' : hsubtype (ob C))
  (a b : ob (full_sub_precategory C')) :
     a --> b -> pr1 a --> pr1 b := @pr1 _ _ .


Lemma isweq_hom_in_precat_from_hom_in_full_subcat (C : precategory)
 (C' : hsubtype (ob C))
    (a b : ob (full_sub_precategory C')):
 isweq (hom_in_precat_from_hom_in_full_subcat _ _ a b).
Proof.
  apply (isweq_iso _
         (hom_in_subcat_from_hom_in_precat _ _ a b)).
  intro f.
  destruct f. simpl.
  apply eq_in_sub_precategory.
  apply idpath.
  intros. apply idpath.
Defined.

Lemma isweq_hom_in_subcat_from_hom_in_precat (C : precategory)
 (C' : hsubtype (ob C))
    (a b : ob (full_sub_precategory C')):
 isweq (hom_in_subcat_from_hom_in_precat  _ _ a b).
Proof.
  apply (isweq_iso _
         (hom_in_precat_from_hom_in_full_subcat _ _ a b)).
  intro f.
  intros. apply idpath.
  intro f.
  destruct f. simpl.
  apply eq_in_sub_precategory.
  apply idpath.
Defined.

Definition weq_hom_in_subcat_from_hom_in_precat (C : precategory)
     (C' : hsubtype (ob C))
    (a b : ob (full_sub_precategory C')): (pr1 a --> pr1 b) ≃ (a-->b) :=
  tpair _ _ (isweq_hom_in_subcat_from_hom_in_precat C C' a b).


Lemma image_is_in_image (C D : precategory) (F : functor C D)
     (a : ob C): is_in_img_functor F (F a).
Proof.
  apply hinhpr.
  exists a.
  apply identity_iso.
Defined.



Lemma functor_full_img_fully_faithful_if_fun_is (C D : precategory)
   (F : functor C D) (H : fully_faithful F) :
   fully_faithful (functor_full_img F).
Proof.
  unfold fully_faithful in *.
  intros a b.
  set (H' := weq_hom_in_subcat_from_hom_in_precat).
  set (H'' := H' D (is_in_img_functor F)).
  set (Fa := tpair (λ a : ob D, is_in_img_functor F a)
        (F a) (image_is_in_image _ _ F a)).
  set (Fb := tpair (λ a : ob D, is_in_img_functor F a)
        (F b) (image_is_in_image _ _ F b)).
  set (H3 := (H'' Fa Fb)).
  assert (H2 : functor_on_morphisms (functor_full_img F) (a:=a) (b:=b) =
                  funcomp (functor_on_morphisms F (a:=a) (b:=b))
                          ((H3))).
  apply funextsec. intro f.
  apply idpath.
  rewrite H2.
  apply (twooutof3c #F H3).
  apply H.
  apply pr2.
Qed.




(** *** Image factorization C -> Img(F) -> D *)

Local Lemma functor_full_img_factorization_ob (C D: precategory)
   (F : functor C D):
  functor_on_objects F =
  functor_on_objects (functor_composite
       (functor_full_img F)
            (sub_precategory_inclusion D _)).
Proof.
  reflexivity.
Defined.


(**  works up to eta conversion *)

(*
Lemma functor_full_img_factorization (C D: precategory)
                (F : functor C D) :
    F = functor_composite _ _ _ (functor_full_img F)
            (sub_precategory_inclusion D _).
Proof.
  apply functor_eq. About functor_full_img_factorization_ob.
  set (H := functor_full_img_factorization_ob C D F).
  simpl in *.
  destruct F as [F Fax].
  simpl.
  destruct F as [Fob Fmor]; simpl in *.
  apply (two_arg_paths_f (H)).
  unfold functor_full_img_factorization_ob in H.
  simpl in *.
  apply dep_funextfun.
  intro a.
  apply dep_funextfun.
  intro b.
  apply funextfun.
  intro f.

  generalize Fmor.
  clear Fax.
  assert (H' : Fob = (λ a : ob C, Fob a)).
   apply H.

  generalize dependent a .
  generalize dependent b.
  clear Fmor.
    generalize H.
  clear H.
  intro H.
  clear H'.
  destruct H.
  tion H.
  induction  H'.
  induction H'.
  clear H.

*)


(** ** Any full subprecategory of a univalent_category is a univalent_category. *)


Section full_sub_cat.

Variable C : precategory.
Hypothesis H : is_univalent C.

Variable C' : hsubtype (ob C).


(** *** Isos in the full subcategory are equivalent to isos in the precategory *)

Lemma iso_in_subcat_is_iso_in_precat (a b : ob (full_sub_precategory C'))
       (f : iso a b): is_iso (C:=C) (a:=pr1 a) (b:=pr1 b)
     (pr1 (pr1 f)).
Proof.
  set (T:= pr1 (inv_from_iso f)).
  apply (is_iso_qinv  _ T).
  unfold T; clear T.
  split; simpl.
  - set (T:=iso_inv_after_iso f).
    apply (base_paths _ _ T).
  - set (T:=iso_after_iso_inv f).
    apply (base_paths _ _ T).
Defined.

Lemma iso_in_precat_is_iso_in_subcat (a b : ob (full_sub_precategory C'))
     (f : iso (pr1 a) (pr1 b)) :
   is_iso (C:=full_sub_precategory C')
     (precategory_morphisms_in_subcat f tt).
Proof.
  apply (is_iso_qinv _ (precategory_morphisms_in_subcat (inv_from_iso f) tt)).
  split; simpl.
  - apply eq_in_sub_precategory; simpl.
    apply iso_inv_after_iso.
  - apply eq_in_sub_precategory; simpl.
    apply iso_after_iso_inv.
Qed.

Definition iso_from_iso_in_sub (a b : ob (full_sub_precategory C'))
       (f : iso a b) : iso (pr1 a) (pr1 b) :=
   tpair _ _ (iso_in_subcat_is_iso_in_precat a b f).

Definition iso_in_sub_from_iso (a b : ob (full_sub_precategory C'))
   (f : iso (pr1 a) (pr1 b)) : iso a b :=
    tpair _ _ (iso_in_precat_is_iso_in_subcat a b f).

Lemma isweq_iso_from_iso_in_sub (a b : ob (full_sub_precategory C')):
     isweq (iso_from_iso_in_sub a b).
Proof.
  apply (isweq_iso _ (iso_in_sub_from_iso a b)).
  intro f.
  apply eq_iso; simpl.
  - apply eq_in_sub_precategory, idpath.
  - intro f; apply eq_iso, idpath.
Defined.

Lemma isweq_iso_in_sub_from_iso (a b : ob (full_sub_precategory C')):
     isweq (iso_in_sub_from_iso a b).
Proof.
  apply (isweq_iso _ (iso_from_iso_in_sub a b)).
  intro f; apply eq_iso, idpath.
  intro f; apply eq_iso; simpl.
  apply eq_in_sub_precategory, idpath.
Defined.




(** *** From Identity in the subcategory to isos in the category  *)
(** This gives a weak equivalence *)

Definition Id_in_sub_to_iso (a b : ob (full_sub_precategory C')):
     a = b -> iso (pr1 a) (pr1 b) :=
       funcomp (@idtoiso _ a b) (iso_from_iso_in_sub a b).

Lemma Id_in_sub_to_iso_equal_iso
  (a b : ob (full_sub_precategory C')) :
    Id_in_sub_to_iso a b = funcomp (total2_paths_hProp_equiv C' a b)
                                    (@idtoiso _ (pr1 a) (pr1 b)).
Proof.
  apply funextfun.
  intro p.
  destruct p.
  apply eq_iso.
  simpl; apply idpath.
Qed.

Lemma isweq_Id_in_sub_to_iso (a b : ob (full_sub_precategory C')):
    isweq (Id_in_sub_to_iso a b).
Proof.
  rewrite Id_in_sub_to_iso_equal_iso.
  apply (twooutof3c _ idtoiso).
  apply pr2.
  apply H.
Defined.

(** *** Decomp of map from id in the subcat to isos in the subcat via isos in ambient precat  *)

Lemma precat_paths_in_sub_as_3_maps
   (a b : ob (full_sub_precategory C')):
     @idtoiso _ a b = funcomp (Id_in_sub_to_iso a b)
                                        (iso_in_sub_from_iso a b).
Proof.
  apply funextfun.
  intro p; destruct p.
  apply eq_iso; simpl.
  unfold precategory_morphisms_in_subcat.
  apply eq_in_sub_precategory, idpath.
Qed.

(** *** The aforementioned decomposed map is a weak equivalence  *)

Lemma isweq_sub_precat_paths_to_iso
  (a b : ob (full_sub_precategory C')) :
 isweq (@idtoiso _ a b).
Proof.
  rewrite precat_paths_in_sub_as_3_maps.
  match goal with |- isweq (funcomp ?f ?g) => apply (twooutof3c f g) end.
  apply isweq_Id_in_sub_to_iso.
  apply isweq_iso_in_sub_from_iso.
Defined.

(** ** Proof of the targeted theorem: full subcats of cats are cats *)

Lemma is_univalent_full_subcat: is_univalent (full_sub_precategory C').
Proof.
  unfold is_univalent.
  split.
  - apply isweq_sub_precat_paths_to_iso.
  - intros x y. apply is_set_sub_precategory_morphisms. apply (pr2 H).
Defined.

End full_sub_cat.

(** The carrier of a subcategory of a univalent category is itself univalent. *)
Definition subcategory_univalent (C : univalent_category) (C' : hsubtype (ob C)) :
  univalent_category.
Proof.
  use mk_category.
  - exact (subcategory C (full_sub_precategory C')).
  - apply is_univalent_full_subcat, univalent_category_is_univalent.
Defined.

Lemma functor_full_img_essentially_surjective (A B : precategory)
     (F : functor A B) :
  essentially_surjective (functor_full_img F).
Proof.
  intro b.
  use (pr2 b).
  intros [c h] q Hq.
  apply Hq.
  exists c.
  apply iso_in_sub_from_iso.
  apply h.
Qed.
