(** ** Precategories in style of essentially algebraic cats *)

(** Of course we later want SETS of objects, rather than types,
    but the construction can already be specified.
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Local Open Scope cat.

Definition total_morphisms (C : precategory_ob_mor) := total2 (
   fun ab : dirprod (ob C)(ob C) =>
        precategory_morphisms (pr1 ab) (pr2 ab)).

Lemma isaset_setcategory_total_morphisms (C : setcategory):
   isaset (total_morphisms C).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  - exact (pr1 (pr2 C)).
  - exact (pr1 (pr2 C)).
  - intro ab; apply ((pr2 (pr2 C)) (dirprod_pr1 ab) (dirprod_pr2 ab)).
Qed.

Definition setcategory_total_morphisms_set (C : setcategory) : hSet :=
    hSetpair _ (isaset_setcategory_total_morphisms C).

Definition precategory_source (C : precategory_ob_mor) :
     total_morphisms C -> ob C :=
     λ abf, pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) :
     total_morphisms C -> ob C :=
     λ abf, pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) :
      ob C -> total_morphisms C :=
      λ c, tpair _ (dirprodpair c c) (identity c).

Definition precategory_total_comp'' (C : precategory_data) :
      ∏ f g : total_morphisms C,
        precategory_target C f = precategory_source C g ->
         total_morphisms C.
Proof.
  intros f g e.
  destruct f as [[a b] f]. simpl in *.
  destruct g as [[b' c] g]. simpl in *.
  unfold precategory_target in e; simpl in e.
  unfold precategory_source in e; simpl in e.
  simpl.
  exists (dirprodpair a c). simpl.
  exact ((f · idtomor _ _ e) · g).
Defined.

Definition precategory_total_comp (C : precategory_data) :
      ∏ f g : total_morphisms C,
        precategory_target C f = precategory_source C g ->
         total_morphisms C :=
  λ f g e,
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f · idtomor _ _ e) · pr2 g).
