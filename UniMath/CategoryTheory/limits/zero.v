(** Direct definition of zero objects *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.

Section def_zero.

  Variable C : precategory.

  Definition isZero (b : C) : UU :=
    (∏ a : C, iscontr (b --> a)) × (∏ a : C, iscontr (a --> b)).

  Lemma isaprop_isZero (b : C) : isaprop (isZero b).
  Proof.
    apply isapropdirprod.
    - apply impred. intros t. apply isapropiscontr.
    - apply impred. intros t. apply isapropiscontr.
  Qed.

  Definition Zero : UU := total2 (λ a, isZero a).

  Definition ZeroObject (Z : Zero) : C := pr1 Z.
  Coercion ZeroObject : Zero >-> ob.

  Definition mk_Zero (b : C) (H : isZero b) : Zero.
  Proof.
    exists b; exact H.
  Defined.

  Definition mk_isZero (b : C) (H : ∏ (a : C), iscontr (b --> a))
             (H' : ∏ (a : C), iscontr (a --> b)) : isZero b.
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
  Qed.

  Lemma ArrowsFromZero (Z : Zero) (b : C) (f g : Z --> b) : f = g.
  Proof.
    apply proofirrelevance.
    apply isapropifcontr.
    apply (pr1 (pr2 Z) _).
  Qed.

  (** For any pair of objects, there exists a unique arrow which factors
    through the zero object *)
  Definition ZeroArrow (Z : Zero) (a b : C) : C⟦a, b⟧ := (ZeroArrowTo Z a) · (ZeroArrowFrom Z b).

  Lemma ZeroArrowEq (Z : Zero) (a b : C) (f1 : C⟦a, Z⟧) (g1 : C⟦Z, b⟧) :
    f1 · g1 = ZeroArrow Z a b.
  Proof.
    rewrite (ArrowsToZero Z a f1 (ZeroArrowTo Z a)).
    rewrite (ArrowsFromZero Z b g1 (ZeroArrowFrom Z b)).
    apply idpath.
  Qed.

  Lemma ZeroArrow_comp_left (Z : Zero) (a b c : C) (f : C⟦b, c⟧) :
    ZeroArrow Z a b · f = ZeroArrow Z a c.
  Proof.
    unfold ZeroArrow at 1. rewrite <- assoc.
    apply ZeroArrowEq.
  Qed.

  Lemma ZeroArrow_comp_right (Z : Zero) (a b c : C) (f : C⟦a, b⟧) :
    f · ZeroArrow Z b c = ZeroArrow Z a c.
  Proof.
    unfold ZeroArrow at 1. rewrite assoc.
    apply ZeroArrowEq.
  Qed.

  Lemma ZeroEndo_is_identity (Z : Zero) (f : Z --> Z) : identity Z = f.
  Proof.
    apply ArrowsToZero.
  Qed.

  Lemma isiso_from_Zero_to_Zero (Z Z' : Zero) :
    is_iso (ZeroArrowTo Z Z').
  Proof.
    apply (is_iso_qinv _ (ZeroArrowTo Z' Z)).
    split; apply pathsinv0; apply ZeroEndo_is_identity.
  Qed.

  Definition iso_Zeros (Z Z' : Zero) : iso Z Z' :=
    tpair _ (ZeroArrowTo Z' Z) (isiso_from_Zero_to_Zero Z' Z).

  Definition z_iso_Zeros (Z Z' : Zero) : z_iso Z Z'.
  Proof.
    use mk_z_iso.
    - exact (ZeroArrowTo Z' Z).
    - exact (ZeroArrowTo Z Z').
    - use mk_is_inverse_in_precat.
      + apply ArrowsFromZero.
      + apply ArrowsFromZero.
  Defined.

  Lemma ZerosArrowEq (Z Z' : Zero) (a b : C) : ZeroArrow Z a b = ZeroArrow Z' a b.
  Proof.
    set (i := iso_Zeros Z Z').
    unfold ZeroArrow.
    assert (e : ZeroArrowTo Z a · identity _ = ZeroArrowTo Z a) by apply id_right.
    rewrite <- e. clear e.
    rewrite <- (iso_inv_after_iso i). rewrite assoc.
    assert (e1 : ZeroArrowTo Z a · i = ZeroArrowTo Z' a) by apply ArrowsToZero.
    rewrite e1. clear e1.
    assert (e2 : inv_from_iso i · ZeroArrowFrom Z b = ZeroArrowFrom Z' b)
      by apply ArrowsFromZero.
    rewrite <- assoc. rewrite e2. clear e2.
    apply idpath.
  Qed.

  Definition hasZero := ishinh Zero.

  Section Zero_Unique.
    Hypothesis H : is_univalent C.

    Lemma isaprop_Zero : isaprop Zero.
    Proof.
      apply invproofirrelevance.
      intros Z Z'.
      apply (total2_paths_f (isotoid _ H (iso_Zeros Z Z'))).
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
  Qed.

  Definition IsoToisZero {A : C} (Z : Zero) (i : iso A Z) :
    isZero A.
  Proof.
    use mk_isZero.
    - intros a.
      use tpair.
      + exact (i · (ZeroArrowFrom Z a)).
      + cbn. intros t.
        apply (pre_comp_with_iso_is_inj
                 C _ _ a (iso_inv_from_iso i) (pr2 (iso_inv_from_iso i))).
        rewrite assoc. cbn. rewrite (iso_after_iso_inv i). rewrite id_left.
        apply ArrowsFromZero.
    - intros a.
      use tpair.
      + exact ((ZeroArrowTo Z a) · (iso_inv_from_iso i)).
      + cbn. intros t.
        apply (post_comp_with_iso_is_inj C _ _ i (pr2 i)).
        rewrite <- assoc. rewrite (iso_after_iso_inv i). rewrite id_right.
        apply ArrowsToZero.
  Qed.


  (** ** Transport of ZeroArrow *)
  Lemma transport_target_ZeroArrow {a b c : C} (Z : Zero) (e : b = c) :
    transportf _ e (ZeroArrow Z a b) = ZeroArrow Z a c.
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_source_ZeroArrow {a b c : C} (Z : Zero) (e : b = a) :
    transportf (λ (a' : ob C), precategory_morphisms a' c) e (ZeroArrow Z b c) = ZeroArrow Z a c.
  Proof.
    induction e. apply idpath.
  Qed.

End def_zero.


Arguments ZeroObject [C] _.
Arguments ZeroArrowTo [C]{Z} b.
Arguments ZeroArrowFrom [C]{Z} b.
Arguments ZeroArrow [C] _ _ _.
Arguments mk_isZero {_} _ _ _ .
Arguments mk_Zero {_} _ _ .
