Require Export UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.

Lemma retract_dec {X Y} (f : X -> Y) (g : Y -> X) (h : f ∘ g ~ idfun Y) : isdeceq X -> isdeceq Y.
Proof.
  intros i y y'. induction (i (g y) (g y')) as [eq|ne].
  - apply ii1. exact (! h y @ maponpaths f eq @ h y').
  - apply ii2. intro p. apply ne. exact (maponpaths g p).
Defined.

Lemma logeq_dec {X Y} : (X <-> Y) -> decidable X -> decidable Y.
Proof.
  intros iff decX. induction iff as [XtoY YtoX].
  induction decX as [x|nx].
  - now apply ii1, XtoY.
  - now apply ii2, (negf YtoX).
Defined.

Definition decidable_prop (X:hProp) := hProppair (decidable X) (isapropdec X (pr2 X)).

(* override LEM of Foundations/Propositions.v, to make an hProp: *)
Definition LEM : hProp := ∀ P : hProp, decidable_prop P.

(*****************************************************************************)
(* all of this stuff about decidable propositions will be redone: *)
(*****************************************************************************)

Definition DecidableProposition : UU := ∑ X : UU, isdecprop X.

Definition isdecprop_to_DecidableProposition {X : UU} (i : isdecprop X) :
  DecidableProposition := X,,i.

Definition decidable_to_isdecprop {X : hProp} : decidable X -> isdecprop X.
Proof.
  intros dec. apply isdecpropif.
  - apply propproperty.
  - exact dec.
Defined.

Definition decidable_to_isdecprop_2 {X : UU} :
  isaprop X -> X ⨿ ¬ X -> isdecprop X.
Proof.
  intros i dec. apply isdecpropif.
  - exact i.
  - exact dec.
Defined.

Definition decidable_to_DecidableProposition {X : hProp} :
  decidable X -> DecidableProposition.
Proof. intros dec. exists X. now apply decidable_to_isdecprop. Defined.

Definition DecidableProposition_to_isdecprop (X : DecidableProposition) :
  isdecprop (pr1 X).
Proof. apply pr2. Defined.

Definition DecidableProposition_to_hProp : DecidableProposition -> hProp.
Proof.
  intros X.
  exact (pr1 X,, isdecproptoisaprop (pr1 X) (pr2 X)).
Defined.
Coercion DecidableProposition_to_hProp : DecidableProposition >-> hProp.
Definition decidabilityProperty (X : DecidableProposition) :
  isdecprop X := pr2 X.

Definition DecidableSubtype (X : UU) : UU := X -> DecidableProposition.
Definition DecidableRelation (X : UU) : UU := X -> X -> DecidableProposition.

Definition decrel_to_DecidableRelation {X : UU} :
  decrel X -> DecidableRelation X.
Proof.
  intros R x y. induction R as [R is]. exists (R x y).
  apply isdecpropif. { apply propproperty. } apply is.
Defined.

Definition decidableAnd (P Q : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (P × Q). apply isdecpropdirprod; apply decidabilityProperty.
Defined.

Definition decidableOr (P Q : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (P ∨ Q). apply isdecprophdisj; apply decidabilityProperty.
Defined.

Lemma neg_isdecprop {X : UU} : isdecprop X -> isdecprop (¬ X).
Proof.
  intros i.
  set (j := isdecproptoisaprop X i).
  apply isdecpropif.
  - apply isapropneg.
  - unfold isdecprop in i.
    set (k := pr1 i).
    induction k as [k|k].
    + apply ii2. now apply todneg.
    + now apply ii1.
Defined.

Definition decidableNot (P : DecidableProposition) : DecidableProposition.
Proof.
  intros. exists (¬ P). apply neg_isdecprop; apply decidabilityProperty.
Defined.

Notation "X ∨ Y" := (decidableOr X Y) (at level 85, right associativity) :
                      decidable_logic.
Notation "A ∧ B" := (decidableAnd A B) (at level 80, right associativity) :
                      decidable_logic.
Notation "'¬' X" := (decidableNot X) (at level 35, right associativity) :
                      decidable_logic.
Delimit Scope decidable_logic with declog.

Ltac choose P yes no := induction (pr1 (decidabilityProperty P)) as [yes|no].

Definition choice {W : UU} : DecidableProposition -> W -> W -> W.
Proof.
  intros P yes no.
  choose P p q.
  - exact yes.
  - exact no.
Defined.

Definition dependent_choice {W : UU} (P : DecidableProposition) :
  (P -> W) -> (¬ P -> W) -> W.
Proof.
  intros yes no.
  choose P p q.
  - exact (yes p).
  - exact (no q).
Defined.

Definition choice_compute_yes {W : UU} (P : DecidableProposition) (p : P)
           (yes no : W) :
  choice P yes no = yes.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. reflexivity.
  - simpl. contradicts p b.
Defined.

Definition choice_compute_no {W : UU} (P : DecidableProposition) (p : ¬ P)
           (yes no : W) :
  choice P yes no = no.
Proof.
  intros.
  unfold choice.
  choose P a b.
  - simpl. contradicts p a.
  - simpl. reflexivity.
Defined.

Definition decidableSubtypeCarrier {X : UU} : DecidableSubtype X -> UU.
Proof. intros S. exact (∑ x, S x). Defined.

Definition decidableSubtypeCarrier' {X : UU} : DecidableSubtype X -> UU.
Proof. intros P.
       (* for use with isfinitedecsubset *)
       exact (hfiber (λ x, choice (P x) true false) true).
Defined.

Definition decidableSubtypeCarrier_weq {X : UU} (P : DecidableSubtype X) :
  decidableSubtypeCarrier' P ≃ decidableSubtypeCarrier P.
Proof.
  intros.
  apply weqfibtototal.
  intros x.
  unfold choice.
  simpl.
  change (pr1 (decidabilityProperty (P x)))
  with (pr1 (decidabilityProperty (P x))).
  choose (P x) p q.
  - simpl. apply weqiff.
    + apply logeq_both_true.
      * reflexivity.
      * assumption.
    + apply isasetbool.
    + apply (propproperty (DecidableProposition_to_hProp _)).
  - simpl. apply weqiff.
    + apply logeq_both_false.
      * exact nopathsfalsetotrue.
      * assumption.
    + apply isasetbool.
    + apply (propproperty (DecidableProposition_to_hProp _)).
Defined.

Definition DecidableSubtype_to_hsubtype {X : UU} (P : DecidableSubtype X) :
  hsubtype X
  := λ x, DecidableProposition_to_hProp (P x).
Coercion DecidableSubtype_to_hsubtype : DecidableSubtype >-> hsubtype.

Definition DecidableRelation_to_hrel {X : UU} (P : DecidableRelation X) : hrel X
  := λ x y, DecidableProposition_to_hProp(P x y).
Coercion DecidableRelation_to_hrel : DecidableRelation >-> hrel.

Definition natlth_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natlthdec.

Definition natleh_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natlehdec.

Definition natgth_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natgthdec.

Definition natgeh_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natgehdec.

Definition nateq_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natdeceq.

Definition natneq_DecidableProposition : DecidableRelation nat :=
  decrel_to_DecidableRelation natdecneq.

Notation " x < y " := (natlth_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.
Notation " x <= y " := (natleh_DecidableProposition x y) (at level 70, no associativity) :
                         decidable_nat.
Notation " x ≤ y " := (natleh_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.
Notation " x ≥ y " := (natgeh_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.
Notation " x ≥ y " := (natgeh_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.
Notation " x > y " := (natgth_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.
Notation " x =? y " := (nateq_DecidableProposition x y) (at level 70, no associativity) :
                         decidable_nat.
Notation " x ≠ y " := (natneq_DecidableProposition x y) (at level 70, no associativity) :
                        decidable_nat.

Delimit Scope decidable_nat with dnat.
