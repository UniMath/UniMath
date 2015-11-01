Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Section def_initial.

Context {C : precategory}.

Definition empty_graph : graph.
Proof.
  exists empty.
  exact (fun _ _ => empty).
Defined.

Definition initDiagram : diagram empty_graph C.
Proof.
exists fromempty.
intros u; induction u.
Defined.

Definition initCocone (c : C) : cocone initDiagram c.
Proof.
refine (mk_cocone _ _); intro v; induction v.
Defined.

Definition isInitial (a : C) :=
  isColimCocone initDiagram a (initCocone a).
 (* forall b : C, iscontr (a --> b). *)

Definition mk_isInitial (a : C) (H : ∀ (b : C), iscontr (a ⇒ b)) :
  isInitial a.
Proof.
intros b cb.
refine (tpair _ _ _).
- exists (pr1 (H b)); intro v; induction v.
- intro t.
  apply subtypeEquality; simpl;
    [intro; apply impred; intro v; induction v|].
  apply (pr2 (H b)).
Defined.

Definition Initial : UU := ColimCocone initDiagram.
(* total2 (fun a => isInitial a). *)

Definition mk_Initial (a : C) (H : isInitial a) : Initial.
Proof.
refine (mk_ColimCocone _ a (initCocone a) _).
apply mk_isInitial.
intro b.
set (x := H b (initCocone b)).
refine (tpair _ _ _).
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
  is_isomorphism (InitialArrow O (InitialObject O')).
Proof.
  apply (is_iso_qinv _ (InitialArrow O' (InitialObject O))).
  split; apply pathsinv0, InitialEndo_is_identity.
Defined.

Definition iso_Initials (O O' : Initial) : iso (InitialObject O) (InitialObject O') :=
   tpair _ (InitialArrow O (InitialObject O')) (isiso_from_Initial_to_Initial O O') .

Definition hasInitial := ishinh Initial.

(* TODO: This should be an instance of a general result for colimits *)
(* Section Initial_Unique. *)

(* Hypothesis H : is_category C. *)

(* Lemma isaprop_Initial : isaprop Initial. *)
(* Proof. *)
(*   apply invproofirrelevance. *)
(*   intros O O'. *)
(*   apply (total2_paths (isotoid _ H (iso_Initials O O')) ). *)
(*   apply proofirrelevance. *)
(*   unfold isInitial. *)
(*   apply impred. *)
(*   intro t ; apply isapropiscontr. *)
(* Qed. *)

(* End Initial_Unique. *)

End def_initial.

Arguments Initial : clear implicits.
Arguments isInitial : clear implicits.

Lemma Initial_from_Colims (C : precategory) :
  Colims C -> Initial C.
Proof.
now intros H; apply H.
Defined.
