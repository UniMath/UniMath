
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

Section def_terminal.

Variable C : precategory.

Definition isTerminal (b : C) := forall a : C, iscontr (a --> b).

Definition Terminal := total2 (fun a => isTerminal a).

Definition TerminalObject (T : Terminal) : C := pr1 T.
Coercion TerminalObject : Terminal >-> ob.

Definition TerminalArrow (T : Terminal) (b : C) : b --> T :=  pr1 (pr2 T b).

Lemma ArrowsToTerminal (T : Terminal) (b : C) (f g : b --> T) : f == g.
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 T _).
Qed.

Lemma TerminalEndo_is_identity (T : Terminal) (f : T --> T) : identity T == f.
Proof.
  apply ArrowsToTerminal.
Qed.

Lemma isiso_from_Terminal_to_Terminal (T T' : Terminal) : 
   is_isomorphism (TerminalArrow T T').
Proof.
  exists (TerminalArrow T' T).
  split; apply pathsinv0;
   apply TerminalEndo_is_identity.
Defined.

Definition iso_Terminals (T T' : Terminal) : iso T T' := 
   tpair _ (TerminalArrow T' T) (isiso_from_Terminal_to_Terminal T' T) .

Definition hasTerminal := ishinh Terminal.

Section Terminal_Unique.

Hypothesis H : is_category C.

Lemma isaprop_Terminal : isaprop Terminal.
Proof.
  apply invproofirrelevance.
  intros T T'.
  apply (total2_paths (isotoid _ H (iso_Terminals T T')) ).
  apply proofirrelevance.
  unfold isTerminal.
  apply impred.
  intro t ; apply isapropiscontr.
Qed.


End Terminal_Unique.

End def_terminal.


(*
Section test.
Variable C : precategory.
Variable T : Terminal C.

Arguments TerminalObject [C]{_}.
Arguments TerminalArrow [C]{T} b.

End test.
*)

Arguments TerminalObject [C]{_}.
Arguments TerminalArrow [C]{T} b.

