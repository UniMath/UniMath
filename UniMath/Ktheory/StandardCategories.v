(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import RezkCompletion.precategories
               Foundations.hlevel2.hSet.
Require Ktheory.Utilities Ktheory.Precategories.
Import RezkCompletion.pathnotations.PathNotations
       Utilities.Notation
       Precategories.Notation.
Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b → c) (f:a → b) : a → c.
Proof. intros. exact (compose f g). Defined.

(** *** the path groupoid *)

Definition is_groupoid (C : precategory) := 
  forall a b : ob C, isweq (fun p : a == b => idtomor a b p).
Lemma isaprop_is_groupoid (C : precategory) : isaprop (is_groupoid C).
Proof. intro. apply impred.
  intro a. apply impred. intro b. apply isapropisweq. Qed.
Lemma morphism_from_iso_is_incl (C : precategory) (a b : ob C) :
  isincl (morphism_from_iso C a b).
Proof. intros ? ? ? g.
  apply (isofhlevelweqf _ (ezweqpr1 _ _)). apply isaprop_is_isomorphism. Qed.
Lemma is_category_groupoid {C : precategory} : is_groupoid C -> is_category C.
Proof. intros ? ig ? ?.
  refine (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _) _ _).
  { refine (isweqhomot (idtomor _ _) _ _ _).
    { intro p. destruct p. reflexivity. }
    apply ig. }
    apply morphism_from_iso_is_incl. Qed.
Definition path_pregroupoid (X:UU) : isofhlevel 3 X -> precategory.
  (* Later we'll define a version of this with no hlevel assumption on X,
     where [mor i j] will be defined with [pi0].  This version will still
     be useful, because in it, each arrow is a path, rather than an
     equivalence class of paths. *)
  intros obj iobj.
  refine (Precategories.makePrecategory obj _ iobj _ _ _ _ _).
  { reflexivity. }
  { intros. exact (f @ g). }
  { reflexivity. }
  { intros. apply pathscomp0rid. }
  { intros. apply Utilities.path_assoc_opaque. }
Defined.
Lemma is_groupoid_path_pregroupoid (X:UU) (iobj:isofhlevel 3 X) :
  is_groupoid (path_pregroupoid X iobj).
Proof. intros ? ? a b.
  assert (k : idfun (a == b) ~ idtomor a b). { intro p. destruct p. reflexivity. }
  apply (isweqhomot _ _ k). apply idisweq. Qed.
Lemma is_category_path_pregroupoid (X:UU) (i:isofhlevel 3 X) :
  is_category (path_pregroupoid X i).
Proof. intros. apply is_category_groupoid. apply is_groupoid_path_pregroupoid.
Qed.
Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
Proof. intros ? iobj. apply (Precategories.category_pair (path_pregroupoid X iobj)). 
  apply is_category_path_pregroupoid. Defined.

(** *** the discrete category on n objects *)

Require Import Foundations.hlevel2.stnfsets.
Definition cat_n (n:nat):category.
  intro. apply (path_groupoid (stn n)). apply hlevelntosn.
  apply isasetstn. Defined.
Definition is_discrete (C:precategory) := 
  dirprod (isaset (ob C)) (is_groupoid C).
Lemma isaprop_is_discrete (C:precategory) : 
  isaprop (is_discrete C).
Proof. intro. apply isofhleveltotal2. apply isapropisaset.
  intro is. apply isaprop_is_groupoid. Qed.
Lemma is_discrete_cat_n (n:nat) : is_discrete (cat_n n).
Proof. intro. split. apply isasetstn. apply is_groupoid_path_pregroupoid. Qed.
