(** * Standard categories *)
(** ** Contents:

- The path groupoid ([path_groupoid])
- The discrete univalent_category on n objects ([cat_n])
  - The category with one object ([unit_category])
  - The category with no objects ([empty_category])
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Open Scope cat.

Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b --> c) (f:a --> b) : a --> c.
Proof. intros. exact (compose f g). Defined.

(** ** The path groupoid *)

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
    use (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _)).
    { use (isweqhomot (idtomor _ _)).
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
  use (makecategory X (λ x y, x = y)); simpl.
  { intros. exact (iobj _ _). }
  { reflexivity. }
  { intros. exact (f @ g). }
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

(** ** The discrete univalent_category on n objects ([cat_n]) *)

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

(** ** The category with one object ([unit_category]) *)

Definition unit_category : univalent_category.
Proof.
  use path_groupoid.
  - exact unit.
  - do 2 (apply hlevelntosn). apply isapropunit.
Defined.

Section FunctorToUnit.
  Context (A : precategory).

  Definition functor_to_unit_data : functor_data A unit_category.
  Proof.
    use mk_functor_data.
    - exact tounit.
    - exact (λ _ _ _, idpath _ ).
  Defined.

  Definition is_functor_to_unit : is_functor functor_to_unit_data.
  Proof.
    split.
    - intro. apply idpath.
    - intros ? ? ? ? ?; apply idpath.
  Qed.

  Definition functor_to_unit : functor A _ := mk_functor _ is_functor_to_unit.

  Lemma iscontr_functor_to_unit : iscontr (functor A unit_category).
  Proof.
    use iscontrpair.
    - exact functor_to_unit.
    - intro F.
      apply functor_eq.
      + apply (homset_property unit_category).
      + use total2_paths_f.
        * apply funextsec. intro. cbn.
          apply proofirrelevance.
          apply isapropunit.
        * do 3 (apply funextsec; intro).
          apply proofirrelevance.
          simpl.
          apply hlevelntosn.
          apply isapropunit.
  Qed.
End FunctorToUnit.

(** ** The category with no objects ([empty_category]) *)

Definition empty_category : univalent_category.
Proof.
  use path_groupoid.
  - exact empty.
  - do 2 (apply hlevelntosn). apply isapropempty.
Defined.

Section FunctorFromEmpty.
  Context (A : precategory).

  Definition functor_from_empty_data : functor_data empty_category A.
  Proof.
    use mk_functor_data.
    - exact fromempty.
    - intros empt ?; induction empt.
  Defined.

  Definition is_functor_from_empty : is_functor functor_from_empty_data.
  Proof.
    use tpair; intro a; induction a.
  Defined.

  Definition functor_from_empty : functor empty_category A :=
    mk_functor _ is_functor_from_empty.

  Lemma iscontr_functor_from_empty {hs : has_homsets A} :
    iscontr (functor empty_category A).
  Proof.
    use iscontrpair.
    - exact functor_from_empty.
    - intro F.
      apply functor_eq; [assumption|].
      use total2_paths_f;
        apply funextsec; intro empt; induction empt.
  Qed.
End FunctorFromEmpty.

(* *)
