(** * Standard categories *)
(** ** Contents:

- The path groupoid ([path_groupoid])
- The discrete univalent_category on n objects ([cat_n])

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Groupoids.
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

Lemma InitialType : Initial type_precat.
Proof.
  apply (mk_Initial (empty : ob type_precat)).
  exact iscontrfunfromempty.
Defined.

Lemma TerminalType : Terminal type_precat.
Proof.
  apply (mk_Terminal (unit : ob type_precat)).
  exact iscontrfuntounit.
Defined.

(** ** The path/fundamental groupoid of a type *)

(** The pregroupoid with points in X as objects and paths as morphisms *)
Definition path_pregroupoid (X:UU) : pregroupoid.
  use mk_pregroupoid.
  - use mk_precategory; use tpair.
    + exact (X,, λ x y, x = y).
    + use dirprodpair.
      * exact (λ _, idpath _).
      * intros a b c; exact pathscomp0.
    + use dirprodpair.
      * reflexivity.
      * intros; apply pathscomp0rid.
    + intros ? ? ? ? ? ?; apply path_assoc.
  - intros x y path.
    use (is_iso_qinv path); cbn in *.
    + exact (!path).
    + use dirprodpair.
      * apply pathsinv0r.
      * apply pathsinv0l.
Defined.

(** If X [isofhlevel] 3, then in particular, its path types are sets *)
Definition has_homsets_path_pregroupoid {X : UU) (iobj : isofhlevel 3 X) :
  has_homsets (path_pregroupoid X).
Proof.
  intros ? ? ? ? ? ?.
  apply iobj.
Defined.

Definition path_groupoid (X : UU) (iobj : isofhlevel 3 X) : groupoid.
Proof.
  use mk_groupoid.
  - use category_pair.
    + exact (path_pregroupoid X).
    + apply (has_homsets_path_pregroupoid); assumption.
  - apply (pregroupoid_is_pregroupoid (path_pregroupoid X)).
Defined.

(** In this case, the path pregroupoid is further univalent. *)
Lemma is_univalent_path_pregroupoid (X : UU) (iobj : isofhlevel 3 X) :
  is_univalent_pregroupoid (path_pregroupoid X).
Proof.
  split.
  - intros a b.
    assert (k : idfun (a = b) ~ idtomor a b).
           { intro p; destruct p; reflexivity. }
    apply (isweqhomot _ _ k). apply idisweq.
  - apply has_homsets_path_pregroupoid; assumption.
Qed.

Lemma is_univalent_path_groupoid (X:UU) (i : isofhlevel 3 X) :
  is_univalent (path_groupoid X i).
Proof.
  intros; split.
  - apply is_univalent_pregroupoid_is_univalent,
          is_univalent_path_pregroupoid; assumption.
  - apply i.
Qed.

Definition path_univalent_groupoid (X : UU) (i3 : isofhlevel 3 X) :
  univalent_category :=
  univalent_category_pair _ (is_univalent_path_groupoid X i3).

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
