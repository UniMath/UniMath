(* In this file, we have formalized the (correct) notion of isomorphisms and univalence of dagger categories.
Notice that these definitions are different compared to (non-dagger) categories, therefore, we can not reuse it. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerIsos.

Local Open Scope cat.

Section DaggerUnivalence.

  Definition idtodaggeriso {C : category} (dag : dagger C)
             (x y : C)
    : x = y -> unitary dag x y.
  Proof.
    intro p ; induction p.
    exact (unitary_id dag x).
  Defined.

  Definition is_univalent_dagger {C : category} (dag : dagger C)
    : UU
    := ∏ x y, isweq (idtodaggeriso dag x y).

  Lemma isaprop_is_univalent_dagger {C : category} (dag : dagger C)
    : isaprop (is_univalent_dagger dag).
  Proof.
    do 2 (apply impred_isaprop ; intro) ; apply isapropisweq.
  Qed.

  Definition daggerisotoid
             {C : category} {dag : dagger C}
             (u : is_univalent_dagger dag) {x y : C}
    : unitary dag x y -> x = y
    := invmap (make_weq _ (u x y)).

  Lemma daggerisotoid_idtodaggeriso
        {C : category} {dag : dagger C}
        (u : is_univalent_dagger dag) {x y : C}
        (p : x = y)
    : daggerisotoid u (idtodaggeriso dag _ _ p) = p.
  Proof.
    apply (homotinvweqweq (make_weq _ (u x y))).
  Qed.

  Lemma idtodaggeriso_daggerisotoid
        {C : category} {dag : dagger C}
        (u : is_univalent_dagger dag) {x y : C}
        (p : unitary dag x y)
    : idtodaggeriso dag _ _ (daggerisotoid u p) = p.
  Proof.
    apply (homotweqinvweq (make_weq _ (u x y))).
  Qed.

End DaggerUnivalence.
