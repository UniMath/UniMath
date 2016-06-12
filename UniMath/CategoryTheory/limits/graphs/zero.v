(** * Zero Objects
  Zero objects are objects of precategory which are both initial objects and
  terminal object. *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.initial.
Require Import UniMath.CategoryTheory.limits.graphs.terminal.

Section def_zero.

  Context {C : precategory}.

  (** Equalities to identity morphisms. *)
  Lemma idtomor_identity_left (c d : C) (e : c = d) :
    (idtomor _ _ e) ;; (idtomor_inv _ _ e) = identity _.
  Proof.
    induction e; simpl.
    apply remove_id_right; apply idpath.
  Defined.

  Lemma idtomor_identity_right (c d : C) (e : c = d) :
    (idtomor_inv _ _  e) ;; (idtomor _ _ e) = identity _.
  Proof.
    induction e; simpl.
    apply remove_id_left; apply idpath.
  Defined.

  (** An object c is zero if it initial and terminal. *)
  Definition isZero (c : C) := (isInitial C c) × (isTerminal C c).

  (** Construction of isZero for an object c from the conditions that the space
    of all morphisms from c to any object d is contractible and and the space of
    all morphisms from any object d to c is contractible. *)
  Definition mk_isZero (c : C) (H : (forall (d : C), iscontr (c --> d))
                                      × (forall (d : C), iscontr (d --> c))) :
    isZero c := mk_isInitial c (dirprod_pr1 H),,mk_isTerminal c (dirprod_pr2 H).

  (** Definition of Zero. *)
  Definition Zero : UU := Σ c : C, isZero c.
  Definition mk_Zero (c : C) (H : isZero c) : Zero := tpair _ c H.
  Definition ZeroObject (Z : Zero) : C := pr1 Z.

  (** Construction of Initial and Terminal from Zero. *)
  Definition Zero_to_Initial (Z : Zero) : Initial C.
  Proof.
    induction Z.
    exact (mk_Initial t (dirprod_pr1 p)).
  Defined.

  Definition Zero_to_Terminal (Z : Zero) : Terminal C.
  Proof.
    induction Z.
    exact (mk_Terminal t (dirprod_pr2 p)).
  Defined.

  (** The following lemmas show that the underlying objects of Initial
    and Terminal, constructed above, are equal to ZeroObject. *)
  Lemma ZeroObject_equals_InitialObject (Z : Zero) :
    ZeroObject Z = InitialObject (Zero_to_Initial Z).
  Proof.
    induction Z; unfold Zero_to_Initial; simpl.
    apply idpath.
  Defined.

  Lemma ZeroObject_equals_TerminalObject (Z : Zero) :
    ZeroObject Z = TerminalObject (Zero_to_Terminal Z).
  Proof.
    induction Z; unfold Zero_to_Terminal; simpl.
    apply idpath.
  Defined.

  (** We construct morphisms from ZeroObject to any other object c and from any
    other object c to the ZeroObject. *)
  Definition ZeroArrowFrom (Z : Zero) (c : C) : C⟦ZeroObject Z, c⟧.
  Proof.
    set (f := InitialArrow (Zero_to_Initial Z) c).
    set (g := idtomor _ _ (ZeroObject_equals_InitialObject Z)).
    exact (g ;; f).
  Defined.

  Definition ZeroArrowTo (Z : Zero) (c : C) : C⟦c, ZeroObject Z⟧.
  Proof.
    set (f := TerminalArrow (Zero_to_Terminal Z) c).
    set (g := idtomor_inv _ _ (ZeroObject_equals_TerminalObject Z)).
    exact (f ;; g).
  Defined.

  (** In particular, we get a zero morphism between any objects. *)
  Definition ZeroArrow (Z : Zero) (c d : C) : C⟦c, d⟧.
  Proof.
    exact (@compose C _ (ZeroObject Z) _ (ZeroArrowTo Z c) (ZeroArrowFrom Z d)).
  Defined.

  (** We show that the above morphisms from ZeroObject and to ZeroObject are
    unique by using uniqueness of morphisms from colimits and uniqueness of
    morphisms to limits. *)
  Lemma ZeroArrowFromUnique (Z : Zero) (c : C) (f : C⟦ZeroObject Z, c⟧) :
    f = (ZeroArrowFrom Z c).
  Proof.
    unfold ZeroArrowFrom.
    set (e := ZeroObject_equals_InitialObject Z).
    assert (H : is_iso (idtomor_inv _ _ e)) by
        (induction e; apply identity_is_iso).
    apply (pre_comp_with_iso_is_inj _ _ _ _ (idtomor_inv _ _ e) H).
    rewrite -> assoc. rewrite idtomor_identity_right.
    rewrite remove_id_left with (g := InitialArrow (Zero_to_Initial Z) c);
      try apply idpath.
    apply colimArrowUnique; intros u; induction u.
  Defined.

  Lemma ZeroArrowToUnique (Z : Zero) (c : C) (f : C⟦c, ZeroObject Z⟧) :
    f = (ZeroArrowTo Z c).
  Proof.
    unfold ZeroArrowTo.
    set (e := ZeroObject_equals_TerminalObject Z).
    assert (H : is_iso (idtomor _ _ e)) by
        (induction e; apply identity_is_iso).
    apply (post_comp_with_iso_is_inj _ _ _ (idtomor _ _ e) H).
    rewrite <- assoc. rewrite idtomor_identity_right.
    rewrite remove_id_right with (g := TerminalArrow (Zero_to_Terminal Z) c);
      try apply idpath.
    apply limArrowUnique; intros u; induction u.
  Defined.

  (** Therefore, any two morphisms from the ZeroObject to an object c are
    equal and any two morphisms from an object c to the ZeroObject are equal. *)
  Corollary ArrowsFromZero (Z : Zero) (c : C) (f g : C⟦ZeroObject Z, c⟧) :
    f = g.
  Proof.
    eapply pathscomp0.
    apply (ZeroArrowFromUnique Z c f).
    apply pathsinv0.
    apply (ZeroArrowFromUnique Z c g).
  Defined.

  Corollary ArrowsToZero (Z : Zero) (c : C) (f g : C⟦c, ZeroObject Z⟧) :
    f = g.
  Proof.
    eapply pathscomp0.
    apply (ZeroArrowToUnique Z c f).
    apply pathsinv0.
    apply (ZeroArrowToUnique Z c g).
  Defined.

  (** It follows that any morphism which factors through 0 is the ZeroArrow. *)
  Corollary ZeroArrowUnique (Z : Zero) (c d : C) (f : C⟦c, ZeroObject Z⟧)
            (g : C⟦ZeroObject Z, d⟧) : f ;; g = ZeroArrow Z c d.
  Proof.
    rewrite (ZeroArrowToUnique Z c f).
    rewrite (ZeroArrowFromUnique Z d g).
    apply idpath.
  Defined.

  (** Compose any morphism with the ZeroArrow and you get the ZeroArrow. *)
  Lemma ZeroArrowLeft (Z : Zero) (a b c : C) (f : C⟦a, b⟧) :
    f ;; ZeroArrow Z b c = ZeroArrow Z a c.
  Proof.
    unfold ZeroArrow at 1. rewrite assoc.
    apply ZeroArrowUnique.
  Defined.

  Lemma ZeroArrowRight (Z : Zero) (a b c : C) (f : C⟦b, c⟧) :
    ZeroArrow Z a b ;; f = ZeroArrow Z a c.
  Proof.
    unfold ZeroArrow at 1. rewrite <- assoc.
    apply ZeroArrowUnique.
  Defined.

  (** An endomorphism of the ZeroObject is the identity morphism. *)
  Corollary ZeroEndo_is_identity (Z : Zero)
            (f : C⟦ZeroObject Z, ZeroObject Z⟧) :
    f = identity (ZeroObject Z).
  Proof.
    apply ArrowsFromZero.
  Defined.

  (** The morphism from ZeroObject to ZeroObject is an isomorphisms. *)
  Lemma isiso_from_Zero_to_Zero (Z Z' : Zero) :
    is_isomorphism (ZeroArrowFrom Z (ZeroObject Z')).
  Proof.
    apply (is_iso_qinv _ (ZeroArrowFrom Z' (ZeroObject Z))).
    split; apply ArrowsFromZero.
  Defined.

  (** Using the above lemma we can construct an isomorphisms between any two
    ZeroObjects. *)
  Definition iso_Zeros (Z Z' : Zero) : iso (ZeroObject Z) (ZeroObject Z') :=
    tpair _ (ZeroArrowFrom Z (ZeroObject Z')) (isiso_from_Zero_to_Zero Z Z').

  Definition hasZero := ishinh Zero.

  (** Construct Zero from Initial and Terminal for which the underlying objects
    are equal. *)
  Definition Initial_and_Terminal_to_Zero
             (I : Initial C) (T : Terminal C)
             (e: InitialObject I = TerminalObject T) : Zero.
  Proof.
    refine (mk_Zero (InitialObject I) _).
    unfold isZero. split.
    - refine (mk_isInitial (InitialObject I) _); intro b.
      + apply iscontrpair with (x := (InitialArrow I b)), InitialArrowUnique.
    - rewrite e. refine (mk_isTerminal (TerminalObject T) _ ); intro a.
      + apply iscontrpair with (x := (TerminalArrow T a)), TerminalArrowUnique.
  Defined.

  (** The following lemma verifies that the ZeroObject of the Zero,
    constructed from Initial and Terminal with InitialObject = TerminalObject,
    equals the InitialObject of the Initial and the TerminalObject of the
    Terminal. *)
  Lemma Initial_and_Terminal_ob_equals_Zero_ob (I : Initial C)
        (T :Terminal C) (e : InitialObject I = TerminalObject T) :
    (InitialObject I = ZeroObject (Initial_and_Terminal_to_Zero I T e))
      × (TerminalObject T = ZeroObject (Initial_and_Terminal_to_Zero I T e)).
  Proof.
    split.
    - apply idpath.
    - apply pathsinv0.
      + assert (ZeroObject (Initial_and_Terminal_to_Zero I T e) =
                InitialObject I) by apply idpath.
        rewrite X. apply e.
  Defined.
End def_zero.

(** Following Initial and Terminal, we clear implicit arguments. *)
Arguments Zero : clear implicits.
Arguments isZero : clear implicits.
