(** * The precategory of types

This file defines the precategory of types in a fixed universe ([type_precat])
and shows that it has some limits and exponentials.

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

- The precategory of types (of a fixed universe) ([type_precat])
- Hom functors
  - As a bifunctor ([hom_functor])
  - Covariant ([cov_hom_functor])
  - Contravariant ([contra_hom_functor])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

(* Hom functors *)
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.
Local Open Scope functions.

(** ** The precategory of types of a fixed universe *)

Definition type_precat : precategory.
Proof.
  use make_precategory.
  - use tpair; use tpair.
    + exact UU.
    + exact (λ X Y, X -> Y).
    + exact (λ X, idfun X).
    + exact (λ X Y Z f g, funcomp f g).
  - repeat split; intros; apply idpath.
Defined.

(** ** Hom functors *)

Section HomFunctors.

  Context {C : precategory}.

  (** ** As a bifunctor [hom_functor] *)

  Definition hom_functor_data :
    functor_data (precategory_binproduct C^op C) type_precat.
  Proof.
    use make_functor_data.
    - intros pair; exact (C ⟦ pr1 pair, pr2 pair ⟧).
    - intros x y fg h.
      refine (_ · h · _).
      + exact (pr1 fg).
      + exact (pr2 fg).
  Defined.

  Lemma is_functor_hom_functor_type : is_functor hom_functor_data.
  Proof.
    use make_dirprod.
    - intro; cbn.
      apply funextsec; intro.
      unfold idfun.
      refine (id_right _ @ _).
      apply id_left.
    - intros ? ? ? ? ?; cbn in *.
      apply funextsec; intro; unfold funcomp.
      abstract (do 3 rewrite assoc; reflexivity).
  Defined.

  Definition hom_functor : functor (precategory_binproduct C^op C) type_precat :=
    make_functor _ is_functor_hom_functor_type.

  Context (c : C).

  (** ** Covariant [cov_hom_functor] *)

  Definition cov_hom_functor : functor C type_precat :=
    functor_fix_fst_arg (C^op) _ _ hom_functor c.

  (** ** Contravariant [contra_hom_functor] *)

  Definition contra_hom_functor : functor (C^op) type_precat :=
    functor_fix_snd_arg (C^op) _ _ hom_functor c.

End HomFunctors.
