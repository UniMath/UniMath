(** * Characterizations of monos, epis, and isos in [HSET] *)

(** ** Contents

  - Epimorphisms are exactly surjective functions [EpisAreSurjective_HSET]
  - Equivalence between isomorphisms and weak equivalences
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.categories.HSET.Core.

Local Open Scope cat.

(** ** Epimorphisms are exactly surjective functions [EpisAreSurjective_HSET] *)

Lemma EpisAreSurjective_HSET {A B : HSET} (f: HSET ⟦ A, B ⟧) (epif : isEpi f)
  : issurjective f.
Proof.
  apply epiissurjectiontosets; [apply setproperty|].
  intros C g1 g2 h .
  apply toforallpaths.
  apply (epif C g1 g2).
  now apply funextfun.
Qed.

(** ** Equivalence between isomorphisms and weak equivalences of two [hSet]s. *)

(** Given an iso, we construct a weak equivalence.
   This is basically unpacking and packing again. *)

Lemma hset_iso_is_equiv (A B : ob HSET)
   (f : iso A B) : isweq (pr1 f).
Proof.
  apply (isweq_iso _ (inv_from_iso f)).
  - intro x.
    set (T:=iso_inv_after_iso f).
    set (T':=toforallpaths _ _ _ T). apply T'.
  - intro x.
    apply (toforallpaths _ _ _ (iso_after_iso_inv f)).
Defined.

Lemma hset_iso_equiv (A B : ob HSET) : iso A B -> (pr1 A) ≃ (pr1 B).
Proof.
  intro f.
  exists (pr1 f).
  apply hset_iso_is_equiv.
Defined.

(** Given a weak equivalence, we construct an iso.
    Again mostly unwrapping and packing.
*)

Lemma hset_equiv_is_iso (A B : hSet)
      (f : (pr1 A) ≃ (pr1 B)) :
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

Lemma hset_equiv_iso (A B : ob HSET) : (pr1 A) ≃ (pr1 B) -> iso A B.
Proof.
  intro f.
  simpl in *.
  exists (pr1 f).
  apply hset_equiv_is_iso.
Defined.

(** Both maps defined above are weak equivalences. *)


Lemma hset_iso_equiv_is_equiv (A B : ob HSET) : isweq (hset_iso_equiv A B).
Proof.
  apply (isweq_iso _ (hset_equiv_iso A B)).
  intro; apply eq_iso.
  - reflexivity.
  - intro; apply subtypeEquality.
    + intro; apply isapropisweq.
    + reflexivity.
Qed.

Definition hset_iso_equiv_weq (A B : ob HSET) : (iso A B) ≃ ((pr1 A) ≃ (pr1 B)).
Proof.
  exists (hset_iso_equiv A B).
  apply hset_iso_equiv_is_equiv.
Defined.

Lemma hset_equiv_iso_is_equiv (A B : ob HSET) : isweq (hset_equiv_iso A B).
Proof.
  apply (isweq_iso _ (hset_iso_equiv A B)).
  { intro f.
    apply subtypeEquality.
    { intro; apply isapropisweq. }
    reflexivity. }
  intro; apply eq_iso.
  reflexivity.
Qed.

Definition hset_equiv_weq_iso (A B : ob HSET) :
  (pr1 A ≃ pr1 B) ≃ iso A B.
Proof.
  exists (hset_equiv_iso A B).
  apply hset_equiv_iso_is_equiv.
Defined.
