(** * Characterizations of monos, epis, and isos in [type_precat] *)

(** ** Contents

  - Injective functions are monic [InjectivesAreMonic_type]
  - Isomorphisms and weak equivalences
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.categories.Type.Core.

Local Open Scope cat.

(** ** Injective functions are monic [InjectivesAreMonic_type] *)

Lemma InjectivesAreMonic_type {A B : UU} (f: type_precat⟦ A, B ⟧) :
      isInjective f -> isMonic f.
Proof.
  intro isI.
  unfold isMonic.
  intros ? ? ? eq.
  apply funextfun; intro.
  apply (invweq (Injectivity _ isI _ _)).
  apply toforallpaths in eq.
  apply eq.
Qed.

(** ** Isomorphisms and weak equivalences *)

(** The following are mostly copied verbatim from
    [CategoryTheory.categories.TYPE.MonoEpiIso]. *)

Lemma type_iso_is_equiv (A B : ob type_precat) (f : iso A B) : isweq (pr1 f).
Proof.
  apply (isweq_iso _ (inv_from_iso f)).
  - intro x.
    set (T:=iso_inv_after_iso f).
    set (T':=toforallpaths _ _ _ T). apply T'.
  - intro x.
    apply (toforallpaths _ _ _ (iso_after_iso_inv f)).
Defined.

Lemma type_iso_equiv (A B : ob type_precat) : iso A B -> A ≃ B.
Proof.
  intro f; use make_weq; [exact (pr1 f)|apply type_iso_is_equiv].
Defined.

(** Given a weak equivalence, we construct an iso. Again mostly unwrapping and
    packing. *)

Lemma type_equiv_is_iso (A B : ob type_precat) (f : A ≃ B) :
           is_iso (C := type_precat) (pr1 f).
Proof.
  apply (is_iso_qinv (C := type_precat) _ (invmap f)).
  split; simpl.
  - apply funextfun; intro; simpl in *.
    unfold compose, identity; simpl.
    apply homotinvweqweq.
  - apply funextfun; intro; simpl in *.
    unfold compose, identity; simpl.
    apply homotweqinvweq.
Defined.

Lemma type_precat_equiv_iso (A B : ob type_precat) : A ≃ B -> iso A B.
Proof.
  intro f.
  use make_iso.
  - exact (pr1 f).
  - apply type_equiv_is_iso.
Defined.

(** Both maps defined above are weak equivalences. *)

Lemma type_iso_equiv_is_equiv (A B : ob type_precat) : isweq (type_iso_equiv A B).
Proof.
  apply (isweq_iso _ (type_precat_equiv_iso A B)).
  intro; apply eq_iso.
  - reflexivity.
  - intro; apply subtypeEquality.
    + intro; apply isapropisweq.
    + reflexivity.
Qed.

Definition type_iso_equiv_weq (A B : ob type_precat) : (iso A B) ≃ (A ≃ B).
Proof.
  exists (type_iso_equiv A B).
  apply type_iso_equiv_is_equiv.
Defined.

Lemma type_equiv_iso_is_equiv (A B : ob type_precat) :
  isweq (type_precat_equiv_iso A B).
Proof.
  apply (isweq_iso _ (type_iso_equiv A B)).
  { intro f.
    apply subtypeEquality.
    { intro; apply isapropisweq. }
    reflexivity. }
  intro; apply eq_iso.
  reflexivity.
Qed.

Definition type_equiv_weq_iso (A B : ob type_precat) :
  (A ≃ B) ≃ iso A B.
Proof.
  exists (type_precat_equiv_iso A B).
  apply type_equiv_iso_is_equiv.
Defined.