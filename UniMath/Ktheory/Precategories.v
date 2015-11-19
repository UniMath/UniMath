(* -*- coding: utf-8 -*- *)

Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.CategoryTheory.precategories
               UniMath.CategoryTheory.opp_precat
               UniMath.CategoryTheory.yoneda
               UniMath.CategoryTheory.category_hset
               UniMath.CategoryTheory.functor_categories .
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.category_hset.
Delimit Scope cat with cat.
Local Open Scope cat.

Arguments id_left [C a b] f.
Arguments id_right [C a b] f.
Arguments assoc [C a b c d] f g h.

Definition Precategory := Σ C:precategory, has_homsets C.
Definition Precategory_pair C h : Precategory := C,,h.
Definition Precategory_to_precategory : Precategory -> precategory := pr1.
Coercion Precategory_to_precategory : Precategory >-> precategory.
Definition homset_property (C:Precategory) : has_homsets C := pr2 C.

Definition SET : Precategory := (hset_precategory,, category_hset.has_homsets_HSET).

Ltac eqn_logic :=
  repeat (
      try intro; try split; try apply id_right; try apply id_left; try apply assoc;
      try apply funextsec; try apply homset_property; try refine (total2_paths _ _);
      try refine (nat_trans_ax _ _ _ _); try refine (! nat_trans_ax _ _ _ _);
      try apply functor_id;
      try apply functor_comp;
      try apply isaprop_is_nat_trans
    ).

Ltac set_logic :=
  repeat (
      try intro; try apply isaset_total2; try apply isasetdirprod; try apply homset_property;
      try apply impred_isaset; try apply isasetaprop).

Definition functorPrecategory (C D:Precategory) : Precategory.
Proof.
  intros. exists (functor_precategory C D (homset_property D)).
  abstract set_logic using L.
Defined.

Notation "[ C , D ]" := (functorPrecategory C D) : cat.

Notation "b ← a" := (precategory_morphisms a b) (at level 50) : cat.
(* agda input \l- or \leftarrow or \<- or \gets or or \l menu *)

Notation "a → b" := (precategory_morphisms a b) (at level 50) : cat.
(* agda input \r- or \to or \-> or \rightarrow or \r menu *)

Notation "a ==> b" := (functor a b) (at level 50) : cat.

Notation "F ⟶ G" := (nat_trans F G) (at level 39) : cat.
(* agda-input \--> or \r-- or \r menu *)

(* Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing) : cat. *)

Notation "g ∘ f" := (precategories.compose f g) (at level 50, left associativity) : cat.
(* agda input \circ *)

Notation "# F" := (functor_on_morphisms F) (at level 3) : cat.

Notation "C '^op'" := (opp_precat C) (at level 3) : cat.

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := C,,i.

Definition Precategory_obmor (C:precategory) : precategory_ob_mor :=
      precategory_ob_mor_from_precategory_data (
          precategory_data_from_precategory C).
Definition Precategory_obj (C:precategory) : Type :=
  ob (
      precategory_ob_mor_from_precategory_data (
          precategory_data_from_precategory C)).
Definition Precategory_mor {C:precategory} : ob C -> ob C -> UU :=
  pr2 (
      precategory_ob_mor_from_precategory_data (
          precategory_data_from_precategory C)).
Notation Hom := Precategory_mor.

Definition Functor_obmor {C D} (F:functor C D) := pr1 F.
Definition Functor_obj {C D} (F:functor C D) := pr1 (pr1 F).
Definition Functor_mor {C D} (F:functor C D) := pr2 (pr1 F).
Definition Functor_identity {C D} (F:functor C D) := functor_id F.
Definition Functor_compose {C D} (F:functor C D) := functor_comp F.

Definition category_pair (C:precategory) (i:is_category C) : category := C,,i.

Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

Definition reflects_isos {C D} (X:C==>D) :=
  ∀ c c' (f : c → c'), is_isomorphism (#X f) -> is_isomorphism f.

Lemma isaprop_reflects_isos {C D} (X:C==>D) : isaprop (reflects_isos X).
Proof.
  intros. apply impred; intros. apply impred; intros. apply impred; intros.
  apply impred; intros. apply isaprop_is_isomorphism. Qed.

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU)
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => mor i j)).
Defined.

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (identity : ∀ i, mor i i)
    (compose : ∀ i j k (f:mor i j) (g:mor j k), mor i k)
    : precategory_data.
  intros.
  exact (precategory_data_pair (makePrecategory_ob_mor obj mor) identity compose).
Defined.

Definition makePrecategory
    (obj : UU)
    (mor : obj -> obj -> UU)
    (homsets : ∀ a b, isaset (mor a b))
    (identity : ∀ i, mor i i)
    (compose : ∀ i j k (f:mor i j) (g:mor j k), mor i k)
    (right : ∀ i j (f:mor i j), compose _ _ _ (identity i) f = f)
    (left  : ∀ i j (f:mor i j), compose _ _ _ f (identity j) = f)
    (associativity : ∀ a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) = compose _ _ _ (compose _ _ _ f g) h)
    : Precategory.
  intros.
  exact ((precategory_pair
           (precategory_data_pair
              (precategory_ob_mor_pair
                 obj
                 (fun i j => mor i j))
              identity compose)
           ((right,,left),,associativity)),,homsets). Defined.

Lemma has_homsets_opp_precat (C: precategory) (hs: has_homsets C) : has_homsets (C^op).
Proof.
  intros C hs a b.
  apply hs.
Qed.

(** *** opposite category of opposite category *)

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C = opp_precat_ob_mor (opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ = maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_data (C : precategory_data)
   : C = opp_precat_data (opp_precat_data C).
Proof. intros [[ob mor] [id co]]. reflexivity. Defined.

Lemma has_homsets_opp_precat_data (C : precategory_data) (hs : has_homsets C) :
  has_homsets (opp_precat_data C).
Proof.
  intros C hs a b.
  apply hs.
Qed.

Lemma has_homsets_opp_precat_opp_precat_data (C : precategory_data)(hs : has_homsets C) :
  has_homsets (opp_precat_data (opp_precat_data C)).
Proof.
  intros C hs a b.
  apply hs.
Qed.

Lemma opp_opp_precat (C : precategory)(hsC: has_homsets (pr1 C)) : C = C^op^op.
Proof. intros.
       apply subtypeEquality'.
       (* the only reason we can't use subtypeEquality is because the homset condition is divorced from the precategory *)
       { apply opp_opp_precat_data. }
       apply isaprop_is_precategory.
       apply has_homsets_opp_precat_opp_precat_data.
       apply hsC.
Defined.
