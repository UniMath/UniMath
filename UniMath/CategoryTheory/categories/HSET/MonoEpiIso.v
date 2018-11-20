(** * Characterizations of monos, epis, and isos in [HSET] *)

(** ** Contents

  - Points as global elements
  - Monomorphisms are exactly injective functions [MonosAreInjective_HSET]
  - Epimorphisms are exactly surjective functions [EpisAreSurjective_HSET]
  - Equivalence between isomorphisms and weak equivalences
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.categories.HSET.Core.

Local Open Scope cat.

(** ** Points as global elements *)

Definition global_element_HSET {A : hSet} (a : A) : HSET⟦unitset, A⟧ := fun _ => a.
(** TODO: I think there is a name in UniMath for the constant function at [a],
    what is it? *)

Definition global_element_HSET_paths_weq {A : hSet} (x y : A) :
  (x = y) ≃ (global_element_HSET x = global_element_HSET y).
Proof.
  apply weqimplimpl.
  - intro.
    apply funextfun; intro; cbn.
    assumption.
  - intros eq.
    apply eqtohomot in eq.
    specialize (eq tt); cbn in eq.
    assumption.
  - apply setproperty.
  - apply setproperty.
Qed.

Definition global_element_HSET_comp {A B : hSet} (f : HSET⟦A, B⟧) (x : A) :
  global_element_HSET x · f = global_element_HSET (f x).
Proof.
  reflexivity.
Qed.

(** This goes through without any further reasoning because of the computational
    behavior of [global_element_HSET] (i.e. [global_element_HSET_comp]). *)
Definition global_element_HSET_fun_weq {A B : hSet} (f : HSET⟦A, B⟧) (x y : A) :
  (f x = f y) ≃ (global_element_HSET x · f = global_element_HSET y · f).
Proof.
  apply global_element_HSET_paths_weq.
Qed.

(** ** Monomorphisms are exactly injective functions [MonosAreInjective_HSET] *)

Lemma MonosAreInjective_HSET {A B : HSET} (f: HSET ⟦ A, B ⟧) :
      isMonic f ≃ isInjective f.
Proof.
  apply weqimplimpl.
  - intro isM.
    apply incl_injectivity; intros b.
    apply invproofirrelevance; intros a1 a2.
    unfold hfiber in *.
    apply subtypeEquality; [intro; apply setproperty|].
    unfold isMonic in *.
    specialize (isM _ (global_element_HSET (pr1 a1)) (global_element_HSET (pr1 a2))).
    apply global_element_HSET_paths_weq.
    apply isM.
    eapply pathscomp0.
    + refine (global_element_HSET_comp _ _ @ _).
      apply global_element_HSET_paths_weq.
      exact (pr2 a1).
    + refine (_ @ !global_element_HSET_comp _ _).
      apply global_element_HSET_paths_weq.
      exact (!pr2 a2).
  - intro isI.
    unfold isMonic.
    intros ? ? ? eq.
    apply funextfun; intro.
    apply (invweq (weqpair _ (isI _ _))).
    apply toforallpaths in eq.
    apply eq.
  - apply isapropisMonic, has_homsets_HSET.
  - apply isaprop_isInjective.
Qed.


(** ** Epimorphisms are exactly surjective functions [EpisAreSurjective_HSET] *)

Lemma EpisAreSurjective_HSET {A B : HSET} (f: HSET ⟦ A, B ⟧) :
      isEpi f ≃ issurjective f.
Proof.
  apply weqimplimpl.
  - intro epif.
    apply epiissurjectiontosets; [apply setproperty|].
    intros ? ? ? ?.
    apply toforallpaths.
    apply epif.
    now apply funextfun.
  - intros is_surj_f.
    intros C g h H.
    apply funextfun; intro.

    (** Get the point [x'] in the fiber above [x] *)
    specialize (is_surj_f x).
    apply (squash_to_prop is_surj_f); [apply setproperty|].
    intro x'.

    (** Replace [x] with [f x'] *)
    refine (!maponpaths _ (hfiberpr2 _ _ x') @ _).
    refine (_ @ maponpaths _ (hfiberpr2 _ _ x')).

    apply toforallpaths in H.
    apply H.
  - apply isapropisEpi.
    apply has_homsets_HSET.
  - apply isapropissurjective.
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
