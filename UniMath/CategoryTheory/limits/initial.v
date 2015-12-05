
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section def_initial.

Variable C : precategory.

Definition isInitial (a : C) := forall b : C, iscontr (a --> b).

Definition Initial := total2 (fun a => isInitial a).

Definition InitialObject (O : Initial) : C := pr1 O.
Coercion InitialObject : Initial >-> ob.

Definition InitialArrow (O : Initial) (b : C) : O --> b :=  pr1 (pr2 O b).

Lemma InitialEndo_is_identity (O : Initial) (f : O --> O) : identity O = f.
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 O O).
Qed.

Lemma InitialArrowUnique (I : Initial) (a : C)
  (f : C⟦InitialObject I,a⟧) : f = InitialArrow I _.
Proof.
  apply (pr2 (pr2 I _ ) _ ).
Defined.


Definition mk_Initial (a : C) (H : isInitial a) : Initial.
Proof.
  exists a.
  exact H.
Defined.

Definition mk_isInitial (a : C) (H : ∀ (b : C), iscontr (a ⇒ b)) :
  isInitial a.
Proof.
  exact H.
Defined.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) :
   is_isomorphism (InitialArrow O O').
Proof.
  apply (is_iso_qinv _ (InitialArrow O' O)).
  split; apply pathsinv0;
   apply InitialEndo_is_identity.
Defined.

Definition iso_Initials (O O' : Initial) : iso O O' :=
   tpair _ (InitialArrow O O') (isiso_from_Initial_to_Initial O O') .

Definition hasInitial := ishinh Initial.

Section Initial_Unique.

Hypothesis H : is_category C.

Lemma isaprop_Initial : isaprop Initial.
Proof.
  apply invproofirrelevance.
  intros O O'.
  apply (total2_paths (isotoid _ H (iso_Initials O O')) ).
  apply proofirrelevance.
  unfold isInitial.
  apply impred.
  intro t ; apply isapropiscontr.
Qed.

End Initial_Unique.


End def_initial.

Arguments Initial : clear implicits.
Arguments isInitial : clear implicits.
Arguments InitialObject {_} _ .
Arguments InitialArrow {_} _ _ .
Arguments InitialArrowUnique {_} _ _ _ .
Arguments mk_isInitial {_} _ _ _ .
Arguments mk_Initial {_} _ _.