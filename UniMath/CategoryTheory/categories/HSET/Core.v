(** * Category of [hSet]s

Started by: Benedikt Ahrens, Chris Kapulkin, Mike Shulman

January 2013

Extended by: Anders Mörtberg (October 2015)

*)

(** ** Contents:

- Category [HSET] of [hSet]s ([hset_category])
- Some particular HSETs

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.HLevels.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.

(** ** Category HSET of [hSet]s ([hset_category]) *)
Section HSET_precategory.

Definition hset_fun_space (A B : hSet) : hSet :=
  make_hSet _ (isaset_set_fun_space A B).

Definition hset_precategory_ob_mor : precategory_ob_mor :=
  tpair (λ ob : UU, ob -> ob -> UU) hSet
        (λ A B : hSet, hset_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  make_precategory_data hset_precategory_ob_mor (fun (A:hSet) (x : A) => x)
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

(* Notation "'HSET'" := hset_precategory : cat. *)
Notation "'HSET'" := hset_category : cat.

(** ** Some particular HSETs *)

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
