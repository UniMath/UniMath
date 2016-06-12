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

  (** Initial objects are colimits of the empty graph and terminal objects are
    limits of the empty graph. Since zero object is both of these, we define
    the diagram needed to construct zero as a limit and a colimit. *)
  Definition empty_graph : graph.
  Proof.
    exists empty.
    exact (fun _ _ => empty).
  Defined.

  Definition zeroDiagram : diagram empty_graph C.
  Proof.
    exists fromempty.
    intros u; induction u.
  Defined.

  (** zero diagram equals initialDiagram and terminalDiagram *)
  Lemma zeroDiagram_equals_initDiagram :
    zeroDiagram = initDiagram.
  Proof.
    apply idpath.
  Defined.

  Lemma zeroDiagram_equals_termDiagram :
    zeroDiagram = termDiagram.
  Proof.
    apply idpath.
  Defined.

  (** Cocone for an object c of zero diagram *)
  Definition zeroCocone (c : C) : cocone zeroDiagram c.
  Proof.
    simple refine (mk_cocone _ _); intro v; induction v.
  Defined.

  (** Cone for an object c of zero diagram *)
  Definition zeroCone (c : C) : cone zeroDiagram c.
  Proof.
    simple refine (mk_cone _ _); intro v; induction v.
  Defined.

  (** An object c is zero if it is both the colimit of zero diagram and the
    limit of zero diagram *)
  Definition isZero (c : C) :=
    (isColimCocone zeroDiagram c (zeroCocone c))
      × (isLimCone zeroDiagram c (zeroCone c)).

  (** Construction of isZero for an object c from the conditions that all
    morphisms from c to any object d is contractible and from any object d to c
    is contractible. *)
   Definition mk_isZero (c : C)
             (H : (forall (d : C), iscontr (c --> d))
                    × (forall (d : C), iscontr (d --> c))) :
    isZero c.
  Proof.
    unfold isZero. split; intros a ca; simple refine (tpair _ _ _).
    - exists (pr1 ((pr1 H) a)); intro v; induction v.
    - intro t.
      apply subtypeEquality; simpl;
        [ intro f; apply impred; intro v; induction v |].
      apply (pr2 ((pr1 H) a)).
    - exists (pr1 ((pr2 H) a)); intro v; induction v.
    - intro t.
      apply subtypeEquality; simpl;
        [ intro f; apply impred; intro v; induction v |].
      apply (pr2 ((pr2 H) a)).
  Defined.

  (** Definition of Zero *)
  Definition Zero : UU :=
    Σ Z : ColimCocone zeroDiagram × LimCone zeroDiagram,
          colim(dirprod_pr1 Z) = lim(dirprod_pr2 Z).
  Definition mk_Zero (c : C) (H : isZero c) : Zero.
  Proof.
    unfold isZero in H. unfold Zero.
    set (Z1 := mk_ColimCocone _ c (zeroCocone c) (dirprod_pr1 H)).
    set (Z2 := mk_LimCone _ c (zeroCone c) (dirprod_pr2 H)).
    assert (e : colim Z1 = lim Z2).
    unfold colim, lim. simpl. apply idpath.
    exact (tpair _ (Z1,,Z2) e).
  Defined.
  Definition ZeroObject (Z : Zero) : C := colim(dirprod_pr1(pr1 Z)).

  (** Equality of zero object with the limit *)
  Lemma ZeroObjectEq (Z : Zero) :
    ZeroObject Z = lim(dirprod_pr2(pr1 Z)).
  Proof.
    apply (pr2 Z).
  Defined.

  (** Equality gives an isomorphism *)
  Lemma ZeroObjectEqIso (Z : Zero) :
    is_iso (idtomor _ _ (ZeroObjectEq Z)).
  Proof.
    induction ZeroObjectEq. apply identity_is_iso.
  Defined.

  (** We construct morphisms from zero object to any other object c and from any
    other object c to the zero object. *)
  Definition ZeroArrowFrom (Z : Zero) (c : C) : C⟦ZeroObject Z, c⟧.
  Proof.
    apply (colimArrow _ _ (zeroCocone c)).
  Defined.

  Definition ZeroArrowTo (Z : Zero) (c : C) : C⟦c, ZeroObject Z⟧.
  Proof.
    induction (pathsinv0 (ZeroObjectEq Z)).
    apply (limArrow _ _ (zeroCone c)).
  Defined.

  (** We show that the above morphisms from and to zero object are uniques by using the
    uniqueness of morphosms from colimits and to limits. *)
  Lemma ZeroArrowFromUnique (Z : Zero) (c : C) (f : C⟦ZeroObject Z, c⟧) :
    f = (ZeroArrowFrom Z c).
  Proof.
    apply colimArrowUnique; intros u; induction u.
  Defined.

  Lemma ZeroArrowToUnique (Z : Zero) (c : C) (f : C⟦c, ZeroObject Z⟧) :
    f = (ZeroArrowTo Z c).
  Proof.
    apply (post_comp_with_iso_is_inj _ _ _ (idtomor _ _ (ZeroObjectEq Z))
                                     (ZeroObjectEqIso Z)).
    eapply pathscomp0.
    apply limArrowUnique with (cc := zeroCone c). intros u; induction u.
    apply pathsinv0.
    apply limArrowUnique. intros u; induction u.
  Defined.

  (** In particular, it follows that any two morphisms from the zero object are
    equal and any two morphisms to the zero object are equal. *)
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

  (** Also, any endomorphism of the zero object must thus be the identity
    morphism. *)
  Corollary ZeroEndo_is_identity (Z : Zero)
            (f : C⟦ZeroObject Z, ZeroObject Z⟧) :
    f = identity (ZeroObject Z).
  Proof.
    apply ArrowsFromZero.
  Defined.

  (** We show that any morphism from zero object to zero object is an
    isomorphisms. *)
  Lemma isiso_from_Zero_to_Zero (Z Z' : Zero) :
    is_isomorphism (ZeroArrowFrom Z (ZeroObject Z')).
  Proof.
    apply (is_iso_qinv _ (ZeroArrowFrom Z' (ZeroObject Z))).
    split; apply ArrowsFromZero.
  Defined.

  (** Using the above lemma we can construct an isomorphisms between any two
    zero objects. *)
  Definition iso_Zeros (Z Z' : Zero) : iso (ZeroObject Z) (ZeroObject Z') :=
    tpair _ (ZeroArrowFrom Z (ZeroObject Z')) (isiso_from_Zero_to_Zero Z Z').

  Definition has_Zeros := ishinh Zero.

  (** We contruct Initial and Terminal from Zero. *)
  Definition Zero_to_Initial (Z : Zero) : (Initial C).
  Proof.
    unfold Initial.
    induction zeroDiagram_equals_initDiagram.
    unfold Zero in Z. induction Z.
    apply (dirprod_pr1 t).
  Defined.

  Definition Zero_to_Terminal (Z : Zero) : (Terminal C).
  Proof.
    unfold Terminal.
    induction zeroDiagram_equals_termDiagram.
    unfold Zero in Z. induction Z.
    apply (dirprod_pr2 t).
  Defined.

  (** The following lemmas show that the InitialObject and TerminalObject of
    the Initial and Terminal contructed from Zero, respectively, are equal
    to the ZeroObject of the Zero. *)
  Lemma Zero_ob_equal_Initial_ob (Z : Zero) :
    ZeroObject Z = InitialObject (Zero_to_Initial Z).
  Proof.
    unfold ZeroObject, InitialObject. unfold colim.
    unfold Zero in Z. unfold Zero_to_Initial.
    induction Z.
    apply idpath.
  Defined.

  Lemma Zero_ob_equal_Terminal_ob (Z : Zero) :
    ZeroObject Z = TerminalObject (Zero_to_Terminal Z).
  Proof.
    unfold ZeroObject, TerminalObject. unfold colim, lim.
    unfold Zero in Z. unfold Zero_to_Terminal.
    induction Z. simpl.
    apply p.
  Defined.

   (** The following lemmas show that two cocones and two cones of zeroDiagram
     with the same object c are equal. *)
  Lemma zeroCocone_isaprop (c : C) : isaprop (cocone zeroDiagram c).
  Proof.
    apply invproofirrelevance.
    unfold cocone. simpl. intros x x'.
    induction x, x'.

    assert (H0 : t = t0).
    apply proofirrelevance.
    apply impred. intros t1. induction t1.
    induction H0.

    assert (H1 : p = p0).
    apply proofirrelevance.
    apply impred. intros t0. induction t0.
    induction H1.

    apply idpath.
  Defined.

  Lemma zeroCone_isaprop (c: C) : isaprop (cone zeroDiagram c).
  Proof.
    apply invproofirrelevance.
    unfold cone. simpl. intros x x'.
    induction x, x'.

    assert (H0 : t = t0).
    apply proofirrelevance.
    apply impred. intros t1. induction t1.
    induction H0.

    assert (H1 : p = p0).
    apply proofirrelevance.
    apply impred. intros t0. induction t0.
    induction H1.

    apply idpath.
  Defined.

  (** Construct Zero from Initial and Terminal for which InitialObject =
    TerminalObject. Here we use the above two lemmas. *)
  Definition Initial_and_Terminal_to_Zero
             (I : Initial C) (T : Terminal C)
             (e: InitialObject I = TerminalObject T) : Zero.
  Proof.
    refine (mk_Zero (InitialObject I) _). unfold isZero.
    induction I. induction t.
    induction T. induction t0.
    unfold InitialObject, TerminalObject in *.
    unfold colim, lim in *.
    simpl in *.
    induction e.
    induction zeroDiagram_equals_initDiagram, zeroDiagram_equals_termDiagram.


    assert (H0 : p0 = zeroCocone t) by apply zeroCocone_isaprop.
    induction H0.
    assert (H1 : p2 = zeroCone t) by apply zeroCone_isaprop.
    induction H1.

    exact (p,,p1).
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
    apply idpath.
    apply pathsinv0.
    assert (ZeroObject (Initial_and_Terminal_to_Zero I T e) = InitialObject I).
    apply idpath.
    rewrite X.
    apply e.
  Defined.
End def_zero.

(** Following Initial and Terminal, we clear implicit arguments. *)
Arguments Zero : clear implicits.
Arguments isZero : clear implicits.
