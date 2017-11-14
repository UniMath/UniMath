(* -*- coding: utf-8 -*- *)

Require Import UniMath.CategoryTheory.Categories
               UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b --> c) (f:a --> b) : a --> c.
Proof. intros. exact (compose f g). Defined.

(** * The precategory of types of a fixed universe *)

Definition type_precat : precategory.
Proof.
  use mk_precategory.
  - use tpair; use tpair.
    + exact UU.
    + exact (λ X Y, X -> Y).
    + exact (λ X, idfun X).
    + exact (λ X Y Z f g, funcomp f g).
  - repeat split; intros; apply idpath.
Defined.

(** *** the path groupoid *)

Definition is_groupoid (C : category) :=
  ∏ a b : ob C, isweq (fun p : a = b => idtomor a b p).

Lemma isaprop_is_groupoid (C : category) : isaprop (is_groupoid C).
Proof. apply impred.
  intro a. apply impred. intro b. apply isapropisweq. Qed.

Lemma morphism_from_iso_is_incl (C : category) (a b : ob C) :
  isincl (morphism_from_iso C a b).
Proof. intro g.
  apply (isofhlevelweqf _ (ezweqpr1 _ _)). apply isaprop_is_iso. Qed.

Lemma is_univalent_groupoid {C : category}: is_groupoid C -> is_univalent C.
Proof. intros ig  .
  split.
  { intros a b.
    refine (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _) _ _).
    { refine (isweqhomot (idtomor _ _) _ _ _).
      { intro p. destruct p. reflexivity. }
      { apply ig. } }
    apply morphism_from_iso_is_incl. }
  { apply homset_property. }
Qed.

Definition path_pregroupoid (X:UU) : isofhlevel 3 X -> category.
  (* Later we'll define a version of this with no hlevel assumption on X,
     where [mor i j] will be defined with [pi0].  This version will still
     be useful, because in it, each arrow is a path, rather than an
     equivalence class of paths. *)
  intros iobj.
  unshelve refine (makecategory X (λ x y, x = y) _ _ _ _ _ _).
  { reflexivity. }
  { intros. exact (f @ g). }
  { intros. exact (iobj _ _). }
  { reflexivity. }
  { intros. apply pathscomp0rid. }
  { intros. apply path_assoc. }
Defined.

Lemma is_groupoid_path_pregroupoid (X:UU) (iobj:isofhlevel 3 X) :
  is_groupoid (path_pregroupoid X iobj).
Proof. intros a b.
  assert (k : idfun (a = b) ~ idtomor a b). { intro p. destruct p. reflexivity. }
  apply (isweqhomot _ _ k). apply idisweq. Qed.

Lemma is_univalent_path_pregroupoid (X:UU) (i:isofhlevel 3 X) :
  is_univalent (path_pregroupoid X i).
Proof.
  intros; split.
  - apply is_univalent_groupoid. apply is_groupoid_path_pregroupoid.
  - apply i.
Qed.

Definition path_groupoid (X:UU) : isofhlevel 3 X -> univalent_category.
Proof. intros iobj. apply (univalent_category_pair (path_pregroupoid X iobj)).
  apply is_univalent_path_pregroupoid. Defined.

(** *** the discrete univalent_category on n objects *)

Require Import UniMath.Combinatorics.StandardFiniteSets.
Definition cat_n (n:nat): univalent_category.
  apply (path_groupoid (stn n)). apply hlevelntosn.
  apply isasetstn. Defined.
Definition is_discrete (C : category) := isaset (ob C) × is_groupoid C.

Lemma isaprop_is_discrete (C : category) :
  isaprop (is_discrete C).
Proof. apply isofhleveltotal2. apply isapropisaset.
  intro is. apply isaprop_is_groupoid. Qed.

Lemma is_discrete_cat_n (n:nat) : is_discrete (cat_n n).
Proof. split. apply isasetstn. apply is_groupoid_path_pregroupoid. Qed.


Definition unit_category : univalent_category.
Proof.
  use path_groupoid.
  - exact unit.
  - do 2 (apply hlevelntosn). apply isapropunit.
Defined.


Section functor.

Variable A : precategory.

Definition functor_to_unit_data : functor_data A unit_category.
Proof.
  exists (λ _, tt).
  exact (λ _ _ _, idpath _ ).
Defined.

Definition is_functor_to_unit : is_functor functor_to_unit_data.
Proof.
  split.
  - intro a. apply idpath.
  - intros a b c f g . apply idpath.
Qed.

Definition functor_to_unit : functor A _ := _ ,, is_functor_to_unit.

Lemma functor_to_unit_unique (F : functor A unit_category)
  : F = functor_to_unit.
Proof.
  apply functor_eq.
  - apply (homset_property unit_category).
  - use total2_paths_f.
    + apply funextsec. intro. cbn.
      apply proofirrelevance.
      apply isapropunit.
    + do 3 (apply funextsec; intro).
      apply proofirrelevance.
      simpl.
      apply hlevelntosn.
      apply isapropunit.
Qed.

End functor.

(* *)