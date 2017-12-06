(** Terminal object defined as a limit *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

Section def_terminal.

Context {C : precategory}.

Definition empty_graph : graph.
Proof.
  exists empty.
  exact (λ _ _, empty).
Defined.

Definition termDiagram : diagram empty_graph C.
Proof.
exists fromempty.
intros u; induction u.
Defined.


Definition termCone (c : C) : cone termDiagram c.
Proof.
use mk_cone; intro v; induction v.
Defined.

Definition isTerminal (a : C) :=
  isLimCone termDiagram a (termCone a).

Definition mk_isTerminal (b : C) (H : ∏ (a : C), iscontr (a --> b)) :
  isTerminal b.
Proof.
intros a ca.
use tpair.
- exists (pr1 (H a)); intro v; induction v.
- intro t.
  apply subtypeEquality; simpl;
    [ intro f; apply impred; intro v; induction v|].
  apply (pr2 (H a)).
Defined.

Definition Terminal : UU := LimCone termDiagram.
(* Definition Terminal := total2 (λ a, isTerminal a). *)

Definition mk_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
use (mk_LimCone _ b (termCone b)).
apply mk_isTerminal.
intro a.
set (x := H a (termCone a)).
use tpair.
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
   is_iso (TerminalArrow T (TerminalObject T')).
Proof.
  apply (is_iso_qinv _ (TerminalArrow T' (TerminalObject T))).
  split; apply pathsinv0, TerminalEndo_is_identity.
Defined.

Definition iso_Terminals (T T' : Terminal) : iso (TerminalObject T) (TerminalObject T') :=
   tpair _ (TerminalArrow T' (TerminalObject T)) (isiso_from_Terminal_to_Terminal T' T) .

Definition hasTerminal := ishinh Terminal.

(* TODO: This should be an instance of a general result for limits *)
(* Section Terminal_Unique. *)

(* Hypothesis H : is_univalent C. *)

(* Lemma isaprop_Terminal : isaprop Terminal. *)
(* Proof. *)
(*   apply invproofirrelevance. *)
(*   intros T T'. *)
(*   apply (total2_paths_f (isotoid _ H (iso_Terminals T T')) ). *)
(*   apply proofirrelevance. *)
(*   unfold isTerminal. *)
(*   apply impred. *)
(*   intro t ; apply isapropiscontr. *)
(* Qed. *)

(* End Terminal_Unique. *)

Definition isTerminal_Terminal (T : Terminal) :
  isTerminal (TerminalObject T).
Proof.
  use mk_isTerminal.
  intros a.
  use tpair.
  - exact (TerminalArrow T a).
  - intros t. use (TerminalArrowUnique T a).
Qed.


(** ** Maps between terminal as a special limit and direct definition *)
Lemma equiv_isTerminal1 (c : C) :
  limits.terminal.isTerminal C c -> isTerminal c.
Proof.
  intros X.
  use mk_isTerminal.
  intros b.
  apply (X b).
Qed.

Lemma equiv_isTerminal2 (c : C) :
  limits.terminal.isTerminal C c <- isTerminal c.
Proof.
  intros X.
  set (XT := mk_Terminal c X).
  intros b.
  use tpair.
  - exact (TerminalArrow XT b).
  - intros t. use (TerminalArrowUnique XT b).
Qed.

Definition equiv_Terminal1 :
  limits.terminal.Terminal C -> Terminal.
Proof.
  intros T.
  exact (mk_Terminal T (equiv_isTerminal1 _ (pr2 T))).
Defined.

Definition equiv_Terminal2 :
  limits.terminal.Terminal C <- Terminal.
Proof.
  intros T.
  exact (limits.terminal.mk_Terminal
           (TerminalObject T)
           (equiv_isTerminal2 _ (isTerminal_Terminal T))).
Defined.

End def_terminal.

Arguments Terminal : clear implicits.
Arguments isTerminal : clear implicits.

Lemma Terminal_from_Lims (C : precategory) :
  Lims_of_shape empty_graph  C -> Terminal C.
Proof.
now intros H; apply H.
Defined.
