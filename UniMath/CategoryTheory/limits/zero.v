(** Direct definition of zero objects *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section def_zero.

  Variable C : precategory.

  Definition isZero (b : C) :=
    (∀ a : C, iscontr (b --> a)) × (∀ a : C, iscontr (a --> b)).

  Definition Zero := total2 (fun a => isZero a).

  Definition ZeroObject (Z : Zero) : C := pr1 Z.
  Coercion ZeroObject : Zero >-> ob.

  Definition mk_Zero (b : C) (H : isZero b) : Zero.
  Proof.
    exists b; exact H.
  Defined.

  Definition mk_isZero (b : C) (H : forall (a : C), iscontr (b --> a))
             (H' : forall (a : C), iscontr (a --> b)) : isZero b.
  Proof.
    unfold isZero.  exact ((H,,H')).
  Defined.

  Definition ZeroArrowFrom (Z : Zero) (b : C) : Z --> b := pr1 (pr1 (pr2 Z) b).
  Definition ZeroArrowTo (Z : Zero) (b : C) : b --> Z := pr1 (pr2 (pr2 Z) b).

  Lemma ArrowsToZero (Z : Zero) (b : C) (f g : b --> Z) : f = g.
  Proof.
    apply proofirrelevance.
    apply isapropifcontr.
    apply (pr2 (pr2 Z) _).
  Defined.

  Lemma ArrowFromZero (Z : Zero) (b : C) (f g : Z --> b) : f = g.
  Proof.
    apply proofirrelevance.
    apply isapropifcontr.
    apply (pr1 (pr2 Z) _).
  Defined.

  Lemma ZeroEndo_is_identity (Z : Zero) (f : Z --> Z) : identity Z = f.
  Proof.
    apply ArrowsToZero.
  Defined.

  Lemma isiso_from_Zero_to_Zero (Z Z' : Zero) :
    is_isomorphism (ZeroArrowTo Z Z').
  Proof.
    apply (is_iso_qinv _ (ZeroArrowTo Z' Z)).
    split; apply pathsinv0; apply ZeroEndo_is_identity.
  Defined.

  Definition iso_Zeros (Z Z' : Zero) : iso Z Z' :=
    tpair _ (ZeroArrowTo Z' Z) (isiso_from_Zero_to_Zero Z' Z).

  Definition hasZero := ishinh Zero.

  Section Zero_Unique.
    Hypothesis H : is_category C.

    Lemma isaprop_Zero : isaprop Zero.
    Proof.
      apply invproofirrelevance.
      intros Z Z'.
      apply (total2_paths (isotoid _ H (iso_Zeros Z Z'))).
      apply proofirrelevance.
      unfold isZero.
      apply isapropdirprod; apply impred; intros t; apply isapropiscontr.
    Defined.

  End Zero_Unique.

  Lemma ZeroIffInitialAndTerminal (b : C) :
    isZero b <-> (isInitial C b) × (isTerminal C b).
  Proof.
    unfold isZero, isInitial, isTerminal.
    split; intros H; apply H.
  Defined.

End def_zero.


Arguments ZeroObject [C] _.
Arguments ZeroArrowTo [C]{Z} b.
Arguments ZeroArrowFrom [C]{Z} b.
Arguments mk_isZero {_} _ _ _ .
Arguments mk_Zero {_} _ _ .