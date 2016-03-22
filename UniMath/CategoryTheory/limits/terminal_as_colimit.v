Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.limits.limits_via_colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Section def_terminal.

Context {C : precategory}.

Definition empty_graph : graph.
Proof.
  exists empty.
  exact (fun _ _ => empty).
Defined.

Definition termDiagram : diagram empty_graph C^op.
Proof.
exists fromempty.
intros u; induction u.
Defined.


Definition termCone (c : C) : cone termDiagram c.
Proof.
simple refine (mk_cocone _ _); intro v; induction v.
Defined.

Definition isTerminal (a : C) :=
  isLimCone termDiagram a (termCone a).

Definition mk_isTerminal (b : C) (H : ∀ (a : C), iscontr (a --> b)) :
  isTerminal b.
Proof.
intros a ca.
simple refine (tpair _ _ _).
- exists (pr1 (H a)); intro v; induction v.
- intro t.
  apply subtypeEquality; simpl;
    [ intro f; apply impred; intro v; induction v|].
  apply (pr2 (H a)).
Defined.

Definition Terminal : UU := LimCone termDiagram.
(* Definition Terminal := total2 (fun a => isTerminal a). *)

Definition mk_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
refine (mk_LimCone _ b (termCone b) _).
apply mk_isTerminal.
intro a.
set (x := H a (termCone a)).
simple refine (tpair _ _ _).
- apply (pr1 x).
- simpl; intro f; apply path_to_ctr; intro v; induction v.
Defined.

Definition TerminalObject (T : Terminal) : C := lim T.
(* Coercion TerminalObject : Terminal >-> ob. *)

Definition TerminalArrow (T : Terminal) (b : C) : C⟦b,TerminalObject T⟧ :=
  limArrow _ _ (termCone b).

Lemma TerminalArrowUnique (T : Terminal) (b : C)
  (f : C⟦b,TerminalObject T⟧) : f = TerminalArrow T _.
Proof.
now apply limArrowUnique; intro v; induction v.
Defined.

Lemma ArrowsToTerminal (T : Terminal) (b : C) (f g : C⟦b,TerminalObject T⟧) : f = g.
Proof.
eapply pathscomp0.
apply TerminalArrowUnique.
now apply pathsinv0, TerminalArrowUnique.
Qed.

Lemma TerminalEndo_is_identity (T : Terminal) (f : C⟦TerminalObject T,TerminalObject T⟧) :
  identity (TerminalObject T) = f.
Proof.
now apply ArrowsToTerminal.
Qed.

Lemma isiso_from_Terminal_to_Terminal (T T' : Terminal) :
   is_isomorphism (TerminalArrow T (TerminalObject T')).
Proof.
  apply (is_iso_qinv _ (TerminalArrow T' (TerminalObject T))).
  split; apply pathsinv0, TerminalEndo_is_identity.
Defined.

Definition iso_Terminals (T T' : Terminal) : iso (TerminalObject T) (TerminalObject T') :=
   tpair _ (TerminalArrow T' (TerminalObject T)) (isiso_from_Terminal_to_Terminal T' T) .

Definition hasTerminal := ishinh Terminal.

(* TODO: This should be an instance of a general result for limits *)
(* Section Terminal_Unique. *)

(* Hypothesis H : is_category C. *)

(* Lemma isaprop_Terminal : isaprop Terminal. *)
(* Proof. *)
(*   apply invproofirrelevance. *)
(*   intros T T'. *)
(*   apply (total2_paths (isotoid _ H (iso_Terminals T T')) ). *)
(*   apply proofirrelevance. *)
(*   unfold isTerminal. *)
(*   apply impred. *)
(*   intro t ; apply isapropiscontr. *)
(* Qed. *)

(* End Terminal_Unique. *)

End def_terminal.

Arguments Terminal : clear implicits.
Arguments isTerminal : clear implicits.

Lemma Terminal_from_Lims (C : precategory) :
  Lims C -> Terminal C.
Proof.
now intros H; apply H.
Defined.
