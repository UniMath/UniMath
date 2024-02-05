(** Definition of initial object as a colimit *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.initial.

Local Open Scope cat.

Section def_initial.

Context {C : category}.

Definition empty_graph : graph.
Proof.
  exists empty.
  exact (λ _ _, empty).
Defined.

Definition initDiagram : diagram empty_graph C.
Proof.
exists fromempty.
intros u; induction u.
Defined.

(** All diagrams over the empty graph are equal *)
Lemma empty_graph_eq_diag (d d' : diagram empty_graph C) :
  eq_diag d d'.
Proof.
  use tpair; use empty_rect.
Defined.

Definition initCocone (c : C) : cocone initDiagram c.
Proof.
use make_cocone; intro v; induction v.
Defined.

Definition isInitial (a : C) :=
  isColimCocone initDiagram a (initCocone a).
 (* ∏ b : C, iscontr (a --> b). *)

Definition make_isInitial (a : C) (H : ∏ (b : C), iscontr (a --> b)) :
  isInitial a.
Proof.
intros b cb.
use tpair.
- exists (pr1 (H b)); intro v; induction v.
- intro t.
  apply subtypePath; simpl;
    [intro; apply impred; intro v; induction v|].
  apply (pr2 (H b)).
Defined.

Definition Initial : UU := ColimCocone initDiagram.
(* total2 (λ a, isInitial a). *)

Definition make_Initial (a : C) (H : isInitial a) : Initial.
Proof.
use (make_ColimCocone _ a (initCocone a)).
apply make_isInitial.
intro b.
set (x := H b (initCocone b)).
use tpair.
- apply (pr1 x).
- simpl; intro f; apply path_to_ctr; intro v; induction v.
Defined.

Definition InitialObject (O : Initial) : C := colim O.
(* Coercion InitialObject : Initial >-> ob. *)

Definition InitialArrow (O : Initial) (b : C) : C⟦InitialObject O,b⟧ :=
  colimArrow _ _ (initCocone b).

Lemma InitialArrowUnique (I : Initial) (a : C)
  (f : C⟦InitialObject I,a⟧) : f = InitialArrow I _.
Proof.
now apply colimArrowUnique; intro v; induction v.
Defined.

Lemma ArrowsFromInitial (I : Initial) (a : C) (f g : C⟦InitialObject I,a⟧) : f = g.
Proof.
eapply pathscomp0.
apply InitialArrowUnique.
now apply pathsinv0, InitialArrowUnique.
Qed.

Lemma InitialEndo_is_identity (O : Initial) (f : C⟦InitialObject O,InitialObject O⟧) :
  identity (InitialObject O) = f.
Proof.
now apply colim_endo_is_identity; intro u; induction u.
Qed.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) :
  is_iso (InitialArrow O (InitialObject O')).
Proof.
  apply (is_iso_qinv _ (InitialArrow O' (InitialObject O))).
  split; apply pathsinv0, InitialEndo_is_identity.
Defined.

Definition iso_Initials (O O' : Initial) : iso (InitialObject O) (InitialObject O') :=
   tpair _ (InitialArrow O (InitialObject O')) (isiso_from_Initial_to_Initial O O') .

Definition hasInitial := ishinh Initial.

(* TODO: This should be an instance of a general result for colimits *)
(* Section Initial_Unique. *)

(* Hypothesis H : is_univalent C. *)

(* Lemma isaprop_Initial : isaprop Initial. *)
(* Proof. *)
(*   apply invproofirrelevance. *)
(*   intros O O'. *)
(*   apply (total2_paths_f (isotoid _ H (iso_Initials O O')) ). *)
(*   apply proofirrelevance. *)
(*   unfold isInitial. *)
(*   apply impred. *)
(*   intro t ; apply isapropiscontr. *)
(* Qed. *)

(* End Initial_Unique. *)

Lemma isInitial_Initial (I : Initial) :
  isInitial (InitialObject I).
Proof.
  use make_isInitial.
  intros b.
  use tpair.
  - exact (InitialArrow I b).
  - intros t. use (InitialArrowUnique I).
Qed.


(** ** Maps between initial as special colimit and direct definition *)
Lemma equiv_isInitial1 (c : C) :
  limits.initial.isInitial C c -> isInitial c.
Proof.
  intros X.
  use make_isInitial.
  intros b.
  apply (X b).
Qed.

Lemma equiv_isInitial2 (c : C) :
  limits.initial.isInitial C c <- isInitial c.
Proof.
  intros X.
  set (XI := make_Initial c X).
  intros b.
  use tpair.
  - exact (InitialArrow XI b).
  - intros t. use (InitialArrowUnique XI b).
Qed.

Definition equiv_Initial1 (c : C) :
  limits.initial.Initial C -> Initial.
Proof.
  intros I.
  use make_Initial.
  - exact I.
  - use equiv_isInitial1.
    exact (pr2 I).
Defined.

Definition equiv_Initial2 (c : C) :
  limits.initial.Initial C <- Initial.
Proof.
  intros I.
  use limits.initial.make_Initial.
  - exact (InitialObject I).
  - use equiv_isInitial2.
    use (isInitial_Initial I).
Defined.

End def_initial.

Arguments Initial : clear implicits.
Arguments isInitial : clear implicits.

Lemma Initial_from_Colims (C : category) :
  Colims_of_shape empty_graph C -> Initial C.
Proof.
now intros H; apply H.
Defined.
