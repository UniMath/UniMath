
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section def_initial.

Variable C : precategory.

Definition isInitial (a : C) := forall b : C, iscontr (a --> b).

Definition Initial := total2 (fun a => isInitial a).

Definition InitialObject (O : Initial) : C := pr1 O.
Coercion InitialObject : Initial >-> ob.

Definition InitialArrow (O : Initial) (b : C) : O --> b :=  pr1 (pr2 O b).

Lemma InitialEndo_is_identity (O : Initial) (f : O --> O) : identity O == f.
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 O O).
Qed.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) : 
   is_isomorphism (InitialArrow O O').
Proof.
  exists (InitialArrow O' O).
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