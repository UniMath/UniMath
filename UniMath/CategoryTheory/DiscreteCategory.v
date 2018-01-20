(** **********************************************************

Contents:

- Definition of the discrete category of a type

Written by: Anders Mörtberg, 2016

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** * Discrete precategories *)
Section Discretecategory.

Variable (A : UU).

Definition discrete_precategory_data : precategory_data.
Proof.
use tpair.
- exact (A,,paths).
- use tpair; [ exact idpath | exact (@pathscomp0 A) ].
Defined.

Definition is_precategory_discrete_precategory_data : is_precategory discrete_precategory_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition discrete_precategory : precategory :=
  (discrete_precategory_data,,is_precategory_discrete_precategory_data).

Lemma has_homsets_discrete_precategory (H : isofhlevel 3 A) : has_homsets discrete_precategory.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

(** To define a functor out of a discrete category it suffices to give a function *)
Lemma functor_discrete_precategory (D : precategory) (f : A → D) :
  functor discrete_precategory D.
Proof.
use tpair.
+ use tpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

(** A natural transformation of functors is given by a family of morphisms *)
Definition is_nat_trans_discrete_precategory {D : precategory} (Dhom : has_homsets D)
           {f g : functor_precategory discrete_precategory D Dhom}
           (F : ∏ x : A , (pr1 f) x --> (pr1 g) x)
  : is_nat_trans (pr1 f) (pr1 g) F.
Proof.
  intros x y h.
  unfold discrete_precategory in h. simpl in h.
  induction h.
  change (idpath x) with (identity x).

  Check (pr1 f).
  assert (k := ! functor_id f x).
  (* The type of k is displayed as [ identity (f x) = # f (identity x) ],
     but neither side of that equation can be typed in: *)
  (* Check (identity (f x)). *)
  (* Check (# f (identity x)). *)
  unfold functor_data_from_functor in k.
  induction k.
  assert (k := ! functor_id g x).
  unfold functor_data_from_functor in k.
  induction k.
  intermediate_path (F x).
  - apply id_left.
  - apply pathsinv0. apply id_right.
Defined.

End Discretecategory.
