(** * HSET is a univalent_category ([is_univalent_HSET]) *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.HLevels.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.

Local Open Scope cat.

(** ** HSET is a univalent_category. *)

Definition univalenceweq (X X' : UU) : (X = X') ≃ (X ≃ X') :=
   tpair _ _ (univalenceAxiom X X').

Definition hset_id_weq_iso (A B : ob HSET) :
  (A = B) ≃ (iso A B) :=
  weqcomp (UA_for_HLevels 2 A B) (hset_equiv_weq_iso A B).


(** The map [precat_paths_to_iso]
    for which we need to show [isweq] is actually
    equal to the carrier of the weak equivalence we
    constructed above.
    We use this fact to show that that [precat_paths_to_iso]
    is an equivalence.
*)

Lemma hset_id_weq_iso_is (A B : ob HSET):
    @idtoiso _ A B = pr1 (hset_id_weq_iso A B).
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
  rewrite hset_id_weq_iso_is.
  apply (pr2 (hset_id_weq_iso A B)).
Defined.

Definition category_HSET : category := make_category HSET has_homsets_HSET.

Lemma is_univalent_HSET : is_univalent category_HSET.
Proof.
  intros a b.
  apply (is_weq_precat_paths_to_iso_hset a b).
Defined.

Definition HSET_univalent_category : univalent_category := _ ,, is_univalent_HSET.
