
(** **********************************************************

Anders Mörtberg

2016


************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section arbitrary_product_precategory.

Variable I : UU.
Variables C : precategory.

Definition arbitrary_product_precategory_ob_mor : precategory_ob_mor.
Proof.
mkpair.
- apply (forall (i : I), ob C).
- intros f g.
  apply (forall i, f i --> g i).
Defined.

Definition arbitrary_product_precategory_data : precategory_data.
Proof.
  exists arbitrary_product_precategory_ob_mor.
  split.
  - intros f i; simpl in *.
    apply (identity (f i)).
  - intros a b c f g i; simpl in *.
    exact (f i ;; g i).
Defined.

Lemma is_precategory_arbitrary_product_precategory_data :
  is_precategory arbitrary_product_precategory_data.
Proof.
repeat split; intros; apply funextsec; intro i.
- apply id_left.
- apply id_right.
- apply assoc.
Qed.

Definition arbitrary_product_precategory : precategory
  := tpair _ _ is_precategory_arbitrary_product_precategory_data.

Definition has_homsets_arbitrary_product_precategory (hsC : has_homsets C) :
  has_homsets arbitrary_product_precategory.
Proof.
intros a b; simpl.
apply impred_isaset; intro i; apply hsC.
Qed.

End arbitrary_product_precategory.

(** Objects and morphisms in the product precategory of two precategories *)
(* Definition prodcatpair {C D : precategory} (X : C) (Y : D) : product_precategory C D. *)
(* Proof. *)
(*   exists X. *)
(*   exact Y. *)
(* Defined. *)

(* Local Notation "A ⊗ B" := (prodcatpair A B) (at level 10). *)

(* Definition prodcatmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z') *)
(*   : X ⊗ Z --> X' ⊗ Z'. *)
(* Proof. *)
(*   exists α. *)
(*   exact β. *)
(* Defined. *)

(* Define pairs of functors and functors from pr1 and pr2 *)
Section functors.

(* Definition pair_functor_data {A B C D : precategory} *)
(*   (F : functor A C) (G : functor B D) : *)
(*   functor_data (product_precategory A B) (product_precategory C D). *)
(* Proof. *)
(* mkpair. *)
(* - intro x; apply (prodcatpair (F (pr1 x)) (G (pr2 x))). *)
(* - intros x y f; simpl; apply (prodcatmor (# F (pr1 f)) (# G (pr2 f))). *)
(* Defined. *)

(* Definition pair_functor {A B C D : precategory} *)
(*   (F : functor A C) (G : functor B D) : *)
(*   functor (product_precategory A B) (product_precategory C D). *)
(* Proof. *)
(* apply (tpair _ (pair_functor_data F G)). *)
(* abstract (split; *)
(*   [ intro x; simpl; rewrite !functor_id; apply idpath *)
(*   | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]). *)
(* Defined. *)

Definition pr_functor_data (I : UU) (C : precategory) (i : I) :
  functor_data (arbitrary_product_precategory I C) C.
Proof.
mkpair.
- intro a; apply (a i).
- intros x y f; simpl; apply (f i).
Defined.

Definition pr_functor (I : UU) (C : precategory) (i : I) :
  functor (arbitrary_product_precategory I C) C.
Proof.
apply (tpair _ (pr_functor_data I C i)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition arbitrary_delta_functor_data (I : UU) (C : precategory) :
  functor_data C (arbitrary_product_precategory I C).
Proof.
mkpair.
- intros x i; apply x.
- intros x y f i; simpl; apply f.
Defined.

Definition arbitrary_delta_functor (I : UU) (C : precategory) :
  functor C (arbitrary_product_precategory I C).
Proof.
apply (tpair _ (arbitrary_delta_functor_data I C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

End functors.