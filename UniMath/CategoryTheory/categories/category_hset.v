(** **********************************************************

Started by: Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013

Extended by: Anders Mörtberg (October 2015)

************************************************************)


(** **********************************************************

Contents:

- Category HSET of hSets ([hset_category])
- HSET is a univalent_category ([is_univalent_HSET])

For structures (like (co)limits) on HSET see
category_hset_structures.v

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.HLevels.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** * category of hSets *)
Section HSET_precategory.

Definition hset_fun_space (A B : hSet) : hSet :=
  hSetpair _ (isaset_set_fun_space A B).

Definition hset_precategory_ob_mor : precategory_ob_mor :=
  tpair (fun ob : UU => ob -> ob -> UU) hSet
        (fun A B : hSet => hset_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  precategory_data_pair hset_precategory_ob_mor (fun (A:hSet) (x : A) => x)
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
Proof.
repeat split.
Qed.

Definition hset_precategory : precategory :=
  tpair _ _ is_precategory_hset_precategory_data.

Local Notation "'HSET'" := hset_precategory : cat.

Lemma has_homsets_HSET : has_homsets HSET.
Proof.
intros a b; apply isaset_set_fun_space.
Qed.

(*
  Canonical Structure hset_precategory. :-)
 *)

Definition hset_category : category := (HSET ,, has_homsets_HSET).

End HSET_precategory.

Notation "'HSET'" := hset_precategory : cat.
Notation "'SET'" := hset_category : cat.

(** * The precategory of hSets is a univalent_category. *)

Section HSET_category.

(** ** Equivalence between isomorphisms and weak equivalences
       of two hsets.
*)

(** Given an iso, we construct a weak equivalence.
   This is basically unpacking and packing again.
*)

Lemma hset_iso_is_equiv (A B : ob HSET)
   (f : iso A B) : isweq (pr1 f).
Proof.
  apply (gradth _ (inv_from_iso f)).
  - intro x.
    set (T:=iso_inv_after_iso f).
    set (T':=toforallpaths _ _ _ T). apply T'.
  - intro x.
    apply (toforallpaths _ _ _ (iso_after_iso_inv f)).
Defined.

Lemma hset_iso_equiv (A B : ob HSET) : iso A B -> weq (pr1 A) (pr1 B).
Proof.
  intro f.
  exists (pr1 f).
  apply hset_iso_is_equiv.
Defined.

(** Given a weak equivalence, we construct an iso.
    Again mostly unwrapping and packing.
*)

Lemma hset_equiv_is_iso (A B : hSet)
      (f : weq (pr1 A) (pr1 B)) :
           is_iso (C:=HSET) (pr1 f).
Proof.
  apply (is_iso_qinv (C:=HSET) _ (invmap f)).
  split; simpl.
  - apply funextfun; intro x; simpl in *.
    unfold compose, identity; simpl.
    apply homotinvweqweq.
  - apply funextfun; intro x; simpl in *.
    unfold compose, identity; simpl.
    apply homotweqinvweq.
Defined.

Lemma hset_equiv_iso (A B : ob HSET) : weq (pr1 A) (pr1 B) -> iso A B.
Proof.
  intro f.
  simpl in *.
  exists (pr1 f).
  apply hset_equiv_is_iso.
Defined.

(** Both maps defined above are weak equivalences. *)


Lemma hset_iso_equiv_is_equiv (A B : ob HSET) : isweq (hset_iso_equiv A B).
Proof.
  apply (gradth _ (hset_equiv_iso A B)).
  intro; apply eq_iso.
  - reflexivity.
  - intro; apply subtypeEquality.
    + intro; apply isapropisweq.
    + reflexivity.
Qed.

Definition hset_iso_equiv_weq (A B : ob HSET) : weq (iso A B) (weq (pr1 A) (pr1 B)).
Proof.
  exists (hset_iso_equiv A B).
  apply hset_iso_equiv_is_equiv.
Defined.

Lemma hset_equiv_iso_is_equiv (A B : ob HSET) : isweq (hset_equiv_iso A B).
Proof.
  apply (gradth _ (hset_iso_equiv A B)).
  { intro f.
    apply subtypeEquality.
    { intro; apply isapropisweq. }
    reflexivity. }
  intro; apply eq_iso.
  reflexivity.
Qed.

Definition hset_equiv_iso_weq (A B : ob HSET) :
  weq (weq (pr1 A) (pr1 B))(iso A B).
Proof.
  exists (hset_equiv_iso A B).
  apply hset_equiv_iso_is_equiv.
Defined.

(** ** HSET is a univalent_category. *)

Definition univalenceweq (X X' : UU) : weq (X = X') (weq X X') :=
   tpair _ _ (univalenceAxiom X X').

Definition hset_id_iso_weq (A B : ob HSET) :
  weq (A = B) (iso A B) :=
  weqcomp (UA_for_HLevels 2 A B) (hset_equiv_iso_weq A B).


(** The map [precat_paths_to_iso]
    for which we need to show [isweq] is actually
    equal to the carrier of the weak equivalence we
    constructed above.
    We use this fact to show that that [precat_paths_to_iso]
    is an equivalence.
*)

Lemma hset_id_iso_weq_is (A B : ob HSET):
    @idtoiso _ A B = pr1 (hset_id_iso_weq A B).
Proof.
  apply funextfun.
  intro p; elim p.
  apply eq_iso; simpl.
  - apply funextfun;
    intro x;
    destruct A.
    apply idpath.
Defined.

Lemma is_weq_precat_paths_to_iso_hset (A B : ob HSET):
   isweq (@idtoiso _ A B).
Proof.
  rewrite hset_id_iso_weq_is.
  apply (pr2 (hset_id_iso_weq A B)).
Defined.

Lemma is_univalent_HSET : is_univalent HSET.
Proof.
  split.
  - apply is_weq_precat_paths_to_iso_hset.
  - apply has_homsets_HSET.
Defined.

End HSET_category.

(* Some particular HSETs *)
Section HSETs.

Definition emptyHSET : HSET.
Proof.
exists empty.
abstract (apply isasetempty).
Defined.

Definition unitHSET : HSET.
Proof.
exists unit.
abstract (apply isasetunit).
Defined.

Definition natHSET : HSET.
Proof.
exists nat.
abstract (apply isasetnat).
Defined.

End HSETs.
