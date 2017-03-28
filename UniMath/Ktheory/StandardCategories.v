(* -*- coding: utf-8 -*- *)

Require Import UniMath.CategoryTheory.precategories
               UniMath.Foundations.Sets.
Require Import UniMath.Ktheory.Utilities UniMath.Ktheory.Precategories.
Local Open Scope cat.

Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b --> c) (f:a --> b) : a --> c.
Proof. intros. exact (compose f g). Defined.

(** *** the path groupoid *)

Definition is_groupoid (C : Precategory) :=
  ∏ a b : ob C, isweq (fun p : a = b => idtomor a b p).

Lemma isaprop_is_groupoid (C : Precategory) : isaprop (is_groupoid C).
Proof. intro. apply impred.
  intro a. apply impred. intro b. apply isapropisweq. Qed.

Lemma morphism_from_iso_is_incl (C : Precategory) (a b : ob C) :
  isincl (morphism_from_iso C a b).
Proof. intros ? ? ? g.
  apply (isofhlevelweqf _ (ezweqpr1 _ _)). apply isaprop_is_iso. Qed.

Lemma is_category_groupoid {C : Precategory}: is_groupoid C -> is_category C.
Proof. intros ? ig  .
  split.
  { intros a b.
    refine (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _) _ _).
    { refine (isweqhomot (idtomor _ _) _ _ _).
      { intro p. destruct p. reflexivity. }
      { apply ig. } }
    apply morphism_from_iso_is_incl. }
  { apply homset_property. }
Qed.

Definition path_pregroupoid (X:UU) : isofhlevel 3 X -> Precategory.
  (* Later we'll define a version of this with no hlevel assumption on X,
     where [mor i j] will be defined with [pi0].  This version will still
     be useful, because in it, each arrow is a path, rather than an
     equivalence class of paths. *)
  intros obj iobj.
  unshelve refine (Precategories.makePrecategory obj (fun x y => x = y) _ _ _ _ _ _).
  { reflexivity. }
  { intros. exact (f @ g). }
  { intros. exact (iobj _ _). }
  { reflexivity. }
  { intros. apply pathscomp0rid. }
  { intros. apply path_assoc. }
Defined.

Lemma is_groupoid_path_pregroupoid (X:UU) (iobj:isofhlevel 3 X) :
  is_groupoid (path_pregroupoid X iobj).
Proof. intros ? ? a b.
  assert (k : idfun (a = b) ~ idtomor a b). { intro p. destruct p. reflexivity. }
  apply (isweqhomot _ _ k). apply idisweq. Qed.

Lemma is_category_path_pregroupoid (X:UU) (i:isofhlevel 3 X) :
  is_category (path_pregroupoid X i).
Proof.
  intros; split.
  - apply is_category_groupoid. apply is_groupoid_path_pregroupoid.
  - apply i.
Qed.

Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
Proof. intros ? iobj. apply (Precategories.category_pair (path_pregroupoid X iobj)).
  apply is_category_path_pregroupoid. Defined.

(** *** the discrete category on n objects *)

Require Import UniMath.Combinatorics.StandardFiniteSets.
Definition cat_n (n:nat):category.
  intro. apply (path_groupoid (stn n)). apply hlevelntosn.
  apply isasetstn. Defined.
Definition is_discrete (C:Precategory) := isaset (ob C) × is_groupoid C.

Lemma isaprop_is_discrete (C:Precategory) :
  isaprop (is_discrete C).
Proof. intro. apply isofhleveltotal2. apply isapropisaset.
  intro is. apply isaprop_is_groupoid. Qed.

Lemma is_discrete_cat_n (n:nat) : is_discrete (cat_n n).
Proof. intro. split. apply isasetstn. apply is_groupoid_path_pregroupoid. Qed.
