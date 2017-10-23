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

Definition LEM : hProp := ∀ P : hProp, decidable_prop P.

(** ** Decidability via complementary pairs *)

Definition ComplementaryPair : UU := ∑ (P Q : UU), complementary P Q.
Definition Part1 (C : ComplementaryPair) : UU := pr1 C.
Definition Part2 (C : ComplementaryPair) : UU := pr1 (pr2 C).
Definition pair_contradiction (C : ComplementaryPair) : Part1 C -> Part2 C -> ∅
  := pr1 (pr2 (pr2 C)).
Definition chooser (C : ComplementaryPair) : Part1 C ⨿ Part2 C
  := pr2 (pr2 (pr2 C)).

Definition isTrue (C : ComplementaryPair)
  := hfiber (@ii1 (Part1 C) (Part2 C)) (chooser C).
Definition isFalse (C : ComplementaryPair)
  := hfiber (@ii2 (Part1 C) (Part2 C)) (chooser C).

Definition  trueWitness {C : ComplementaryPair} : isTrue  C -> Part1 C := pr1.
Definition falseWitness {C : ComplementaryPair} : isFalse C -> Part2 C := pr1.

Coercion  trueWitness : isTrue  >-> Part1.
Coercion falseWitness : isFalse >-> Part2.

Lemma complementaryDecisions (C : ComplementaryPair) :
  iscontr (isTrue C ⨿ isFalse C).
Proof.
  (* the idea of this proof is to show that [isTrue C ⨿ isFalse C] is the same
     as the decomposition provided by [weqcoprodsplit] *)
  intros.
  apply iscontrifweqtounit. assert (w := weqcoprodsplit (λ _:unit, chooser C)).
  apply invweq. apply (weqcomp w). apply weqcoprodf; apply weqhfiberunit.
Defined.

Lemma isaprop_isTrue (C : ComplementaryPair) : isaprop (isTrue C).
(* No axioms are used. *)
Proof.
  intros.
  apply (isapropcomponent1 (isTrue C) (isFalse C)).
  apply isapropifcontr.
  apply complementaryDecisions.
Defined.

Lemma isaprop_isFalse (C : ComplementaryPair) : isaprop (isFalse C).
(* No axioms are used. *)
(* By contrast, to prove [¬P] is a proposition requires the use of functional
   extensionality. *)
Proof.
  intros.
  apply (isapropcomponent2 (isTrue C) (isFalse C)).
  apply isapropifcontr.
  apply complementaryDecisions.
Defined.

Ltac unpack_pair C P Q con c := induction C as [P Qc]; induction Qc as [Q c];
                                induction c as [con c]; simpl in c, P, Q.

Lemma pair_truth (C : ComplementaryPair) : Part1 C -> isTrue C.
Proof.
  intros p.
  unpack_pair C P Q con c;
    unfold isTrue, hfiber, Part1, Part2, chooser in *; simpl in *.
  induction c as [p'|q].
  - now exists p'.
  - apply fromempty. contradicts (con p) q.
Defined.

Lemma pair_falsehood (C : ComplementaryPair) : Part2 C -> isFalse C.
Proof.
  intros q.
  unpack_pair C P Q con c;
    unfold isFalse, hfiber, Part1, Part2, chooser in *; simpl in *.
  induction c as [p|q'].
  - apply fromempty. contradicts (con p) q.
  - now exists q'.
Defined.

Definition to_ComplementaryPair {P : UU} (c : P ⨿ neg P) : ComplementaryPair
  (* By using [isTrue _] instead, we're effectively replacing P by a
     propositional subtype of it: *)
  (* the part connected to the element of [P ⨿ ¬P]. *)
  (* Similarly, by using [isFalse _] instead, we're effectively replacing [¬P]
     by a propositional subtype of it.  *)
  (* Both are proved to be propositions without [funextemptyAxiom] *)
  := (P,,neg P,,(λ p n, n p),,c).

(* Relate isolated points to complementary pairs *)

Definition isolation {X : UU} (x : X) (is : isisolated X x) (y : X) : UU
  := isFalse (to_ComplementaryPair (is y)).

Definition isaprop_isolation {X : UU} (x : X) (is : isisolated X x) (y : X) :
  isaprop (isolation x is y) := isaprop_isFalse _.

Definition isolation_to_inequality {X : UU} (x : X) (is : isisolated X x)
           (y : X) :
  isolation x is y -> x != y := falseWitness.

Definition inequality_to_isolation {X : UU} (x : X) (i : isisolated X x)
           (y : X) :
  x != y -> isolation x i y := pair_falsehood (to_ComplementaryPair (i y)).

(* operations on complementary pairs *)

Definition pairNegation (C : ComplementaryPair) : ComplementaryPair
  := Part2 C,, Part1 C ,, (λ q p, pair_contradiction C p q),,
           coprodcomm _ _ (chooser C).

Definition pairConjunction (C C' : ComplementaryPair) : ComplementaryPair.
Proof.
  unpack_pair C P Q con c; unpack_pair C' P' Q' con' c'; simpl in *.
  unfold ComplementaryPair. exists (P × P'); exists (Q ⨿ Q'). split.
  - simpl. intros a b. induction a as [p p']. induction b as [b|b].
    + induction c' as [_|q'].
      * contradicts (con p) b.
      * contradicts (con p) b.
    + contradicts (con' p') b.
  - simpl. induction c as [p|q].
    + induction c' as [p'|q'].
      * apply ii1. exact (p,,p').
      * apply ii2, ii2. exact q'.
    + induction c' as [p'|q'].
      * apply ii2, ii1. exact q.
      * apply ii2, ii2. exact q'.
Defined.

Definition pairDisjunction (C C' : ComplementaryPair) : ComplementaryPair.
Proof.
  intros.
  exact (pairNegation (pairConjunction (pairNegation C) (pairNegation C'))).
Defined.

Definition dnegelim {P Q : UU} : complementary P Q -> ¬¬ P -> P.
Proof.
  intros c nnp. induction c as [n c].
  induction c as [p|q].
  - assumption.
  - contradicts nnp (λ p, n p q).
Defined.

(* Law of Excluded Middle

   We don't state LEM as an axiom, because we want to force it
   to be a hypothesis of any corollaries of any theorems that
   appeal to it. *)

Lemma LEM_for_sets (X : UU) : LEM -> isaset X -> isdeceq X.
Proof. intros lem is x y. exact (lem (hProppair (x = y) (is x y))). Defined.

Lemma isaprop_LEM : isaprop LEM.
Proof.
  unfold LEM. apply impred_isaprop; intro P. apply isapropdec. apply propproperty.
Defined.

Lemma dneg_LEM (P : hProp) : LEM -> ¬¬ P -> P.
Proof. intros lem. exact (dnegelim ((λ p np, np p),,lem P)). Defined.

Corollary reversal_LEM (P Q : hProp) : LEM -> (¬ P -> Q) -> (¬ Q -> P).
Proof.
  intros lem f n.
  assert (g := negf f); clear f.
  assert (h := g n); clear g n.
  apply (dneg_LEM _ lem).
  exact h.
Defined.

(*****************************************************************************)
(* all of this stuff about decidable propositions will be replaced by the better code above *)
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
