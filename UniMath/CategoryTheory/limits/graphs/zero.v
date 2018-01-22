(** * Zero Objects
  Zero objects are objects of precategory which are both initial objects and
  terminal object. *)
(** ** Contents
- Definition of Zero
- Coincides with the direct definition
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.initial.
Require Import UniMath.CategoryTheory.limits.graphs.terminal.
Require Import UniMath.CategoryTheory.limits.zero.


(** * Definition of zero using limits and colimits *)
Section def_zero.

  Context {C : precategory}.

  (** An object c is zero if it initial and terminal. *)
  Definition isZero (c : C) : UU := (isInitial C c) × (isTerminal C c).

  (** Construction of isZero for an object c from the conditions that the space
    of all morphisms from c to any object d is contractible and and the space of
    all morphisms from any object d to c is contractible. *)
  Definition mk_isZero (c : C) (H : (∏ (d : C), iscontr (c --> d))
                                      × (∏ (d : C), iscontr (d --> c))) :
    isZero c := mk_isInitial c (dirprod_pr1 H),,mk_isTerminal c (dirprod_pr2 H).

  (** Definition of Zero. *)
  Definition Zero : UU := ∑ c : C, isZero c.
  Definition mk_Zero (c : C) (H : isZero c) : Zero := tpair _ c H.
  Definition ZeroObject (Z : Zero) : C := pr1 Z.

  (** Construction of Initial and Terminal from Zero. *)
  Definition Zero_to_Initial (Z : Zero) : Initial C :=
    mk_Initial (pr1 Z) (dirprod_pr1 (pr2 Z)).
  Definition Zero_to_Terminal (Z : Zero) : Terminal C :=
    mk_Terminal (pr1 Z) (dirprod_pr2 (pr2 Z)).

  (** The following lemmas show that the underlying objects of Initial
    and Terminal, constructed above, are equal to ZeroObject. *)
  Lemma ZeroObject_equals_InitialObject (Z : Zero) :
    ZeroObject Z = InitialObject (Zero_to_Initial Z).
  Proof.
    apply idpath.
  Defined.

  Lemma ZeroObject_equals_TerminalObject (Z : Zero) :
    ZeroObject Z = TerminalObject (Zero_to_Terminal Z).
  Proof.
    apply idpath.
  Defined.

  (** We construct morphisms from ZeroObject to any other object c and from any
    other object c to the ZeroObject. *)
  Definition ZeroArrowFrom (Z : Zero) (c : C) : C⟦ZeroObject Z, c⟧ :=
    InitialArrow (Zero_to_Initial Z) c.
  Definition ZeroArrowTo (Z : Zero) (c : C) : C⟦c, ZeroObject Z⟧ :=
    TerminalArrow (Zero_to_Terminal Z) c.

  (** In particular, we get a zero morphism between any objects. *)
  Definition ZeroArrow (Z : Zero) (c d : C) : C⟦c, d⟧ :=
    @compose C _ (ZeroObject Z) _ (ZeroArrowTo Z c) (ZeroArrowFrom Z d).

  (** We show that the above morphisms from ZeroObject and to ZeroObject are
    unique by using uniqueness of the morphism from InitialObject and uniqueness
    of the morphism to TerminalObject. *)
  Lemma ZeroArrowFromUnique (Z : Zero) (c : C) (f : C⟦ZeroObject Z, c⟧) :
    f = (ZeroArrowFrom Z c).
  Proof.
    apply (InitialArrowUnique (Zero_to_Initial Z) c f).
  Defined.

  Lemma ZeroArrowToUnique (Z : Zero) (c : C) (f : C⟦c, ZeroObject Z⟧) :
    f = (ZeroArrowTo Z c).
  Proof.
    apply (TerminalArrowUnique (Zero_to_Terminal Z) c f).
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
            (g : C⟦ZeroObject Z, d⟧) : f · g = ZeroArrow Z c d.
  Proof.
    rewrite (ZeroArrowToUnique Z c f).
    rewrite (ZeroArrowFromUnique Z d g).
    apply idpath.
  Defined.

  (** Compose any morphism with the ZeroArrow and you get the ZeroArrow. *)
  Lemma precomp_with_ZeroArrow (Z : Zero) (a b c : C) (f : C⟦a, b⟧) :
    f · ZeroArrow Z b c = ZeroArrow Z a c.
  Proof.
    unfold ZeroArrow at 1. rewrite assoc.
    apply ZeroArrowUnique.
  Defined.

  Lemma postcomp_with_ZeroArrow (Z : Zero) (a b c : C) (f : C⟦b, c⟧) :
    ZeroArrow Z a b · f = ZeroArrow Z a c.
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
    is_iso (ZeroArrowFrom Z (ZeroObject Z')).
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
    are isomorphic. *)
  Definition Initial_and_Terminal_to_Zero
             (I : Initial C) (T : Terminal C)
             (e: iso (InitialObject I) (TerminalObject T)) : Zero.
  Proof.
    use (mk_Zero (InitialObject I)).
    split.
    - use (mk_isInitial (InitialObject I)); intro b.
      apply iscontrpair with (x := (InitialArrow I b)), InitialArrowUnique.
    - use (mk_isTerminal (InitialObject I)); intro a.
      apply (iscontrretract (postcomp_with (inv_from_iso e))
                            (postcomp_with (morphism_from_iso _ _ _  e))).
      intros y. unfold postcomp_with.
      rewrite <- assoc. rewrite (iso_inv_after_iso e).
      apply (remove_id_right _ _ _ y y _ (idpath _) (idpath _)).
      apply (iscontrpair (TerminalArrow T a)), TerminalArrowUnique.
  Defined.

  (** The following lemma verifies that the ZeroObject of the Zero,
    constructed from Initial and Terminal with InitialObject isomorphic to
    TerminalObject, is isomorphic to the InitialObject and isomorphic to the
    TerminalObject. *)
  Lemma Initial_and_Terminal_ob_equals_Zero_ob (I : Initial C)
        (T :Terminal C) (e : iso (InitialObject I) (TerminalObject T)) :
    (iso (InitialObject I) (ZeroObject (Initial_and_Terminal_to_Zero I T e)))
      × (iso (TerminalObject T)
             (ZeroObject (Initial_and_Terminal_to_Zero I T e))).
  Proof.
    exact(identity_iso (InitialObject I),,iso_inv_from_iso e).
  Defined.

End def_zero.

(** * Zero coincides with the direct definition *)
Section zero_coincides.

  Context {C : precategory}.

  (** ** isZero *)

  Lemma equiv_isZero1 (c : C) :
    limits.zero.isZero C c -> isZero c.
  Proof.
    intros X.
    use mk_isZero.
    split.
    - intros d. apply ((pr1 X) d).
    - intros d. apply ((pr2 X) d).
  Qed.

  Lemma equiv_isZero2 (c : C) :
    limits.zero.isZero C c <- isZero c.
  Proof.
    intros X.
    set (XZ := mk_Zero c X).

    split.
    - intros b.
      use tpair.
      apply (InitialArrow (Zero_to_Initial XZ) b).
      intros t.
      use (InitialArrowUnique (Zero_to_Initial XZ) b).
    - intros a.
      use tpair.
      apply (TerminalArrow (Zero_to_Terminal XZ) a).
      intros t.
      use (TerminalArrowUnique (Zero_to_Terminal XZ) a).
  Qed.

  (** ** Zero **)

  Definition equiv_Zero1 :
    limits.zero.Zero C -> @Zero C.
  Proof.
    intros Z.
    exact (mk_Zero Z (equiv_isZero1 _ (pr2 Z))).
  Defined.

  Definition equiv_Zero2 :
    limits.zero.Zero C <- @Zero C.
  Proof.
    intros Z.
    exact (limits.zero.mk_Zero
             (ZeroObject Z)
             (equiv_isZero2
                _ ((isInitial_Initial (Zero_to_Initial Z))
                     ,,(isTerminal_Terminal (Zero_to_Terminal Z))))).
  Defined.

  (** ** Arrows *)

  Lemma equiv_ZeroArrowTo (x : C) (Z : Zero) :
    @limits.zero.ZeroArrowTo C (equiv_Zero2 Z) x = ZeroArrowTo Z x.
  Proof.
    apply ZeroArrowToUnique.
  Qed.

  Lemma equiv_ZeroArrowFrom (x : C) (Z : Zero) :
    @limits.zero.ZeroArrowFrom C (equiv_Zero2 Z) x = ZeroArrowFrom Z x.
  Proof.
    apply ZeroArrowFromUnique.
  Qed.

  Lemma equiv_ZeroArrow (x y : C) (Z : Zero) :
    @limits.zero.ZeroArrow C (equiv_Zero2 Z) x y = ZeroArrow Z x y.
  Proof.
    unfold limits.zero.ZeroArrow. unfold ZeroArrow.
    rewrite equiv_ZeroArrowTo.
    rewrite equiv_ZeroArrowFrom.
    apply idpath.
  Qed.

End zero_coincides.


(** Following Initial and Terminal, we clear implicit arguments. *)
Arguments Zero : clear implicits.
Arguments isZero : clear implicits.
