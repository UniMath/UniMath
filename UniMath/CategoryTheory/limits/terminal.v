(**

Direct definition of terminal object together with:

- A proof that the terminal object is a property in a (saturated/univalent) category ([isaprop_Terminal])
- Construction of the terminal object from the empty product ([terminal_from_empty_product])


*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Local Open Scope cat.

Section def_terminal.

Variable C : precategory.

Definition isTerminal (b : C) : UU := ∏ a : C, iscontr (a --> b).

Definition Terminal : UU := total2 (fun a => isTerminal a).

Definition TerminalObject (T : Terminal) : C := pr1 T.
Coercion TerminalObject : Terminal >-> ob.

Definition mk_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
  exists b; exact H.
Defined.

Definition mk_isTerminal (b : C) (H : ∏ (a : C), iscontr (a --> b)) :
  isTerminal b.
Proof.
  exact H.
Defined.

Definition TerminalArrow (T : Terminal) (b : C) : b --> T :=  pr1 (pr2 T b).

Lemma ArrowsToTerminal (T : Terminal) (b : C) (f g : b --> T) : f = g.
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (pr2 T _).
Qed.

Lemma TerminalEndo_is_identity (T : Terminal) (f : T --> T) : identity T = f.
Proof.
  apply ArrowsToTerminal.
Qed.

Lemma isiso_from_Terminal_to_Terminal (T T' : Terminal) :
   is_isomorphism (TerminalArrow T T').
Proof.
  apply (is_iso_qinv _ (TerminalArrow T' T)).
  split.
  - apply pathsinv0. apply TerminalEndo_is_identity.
  - apply pathsinv0. apply TerminalEndo_is_identity.
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
  apply (total2_paths_f (isotoid _ H (iso_Terminals T T')) ).
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

Arguments TerminalObject [C] _.
Arguments TerminalArrow [C]{T} b.
Arguments mk_isTerminal {_} _ _ _ .
Arguments mk_Terminal {_} _ _.


Section Terminal_and_EmptyProd.
  Require Import UniMath.CategoryTheory.limits.products.

  (** Construct Terminal from empty arbitrary product. *)
  Definition terminal_from_empty_product (C : precategory) :
    ProductCone empty C fromempty -> Terminal C.
  Proof.
    intros X.
    refine (mk_Terminal (ProductObject _ C X) _).
    refine (mk_isTerminal _ _).
    intros a.
    assert (H : ∏ i : empty, C⟦a, fromempty i⟧) by
        (intros i; apply (fromempty i)).
    apply (iscontrpair (ProductArrow _ _ X H)); intros t.
    apply ProductArrowUnique; intros i; apply (fromempty i).
  Defined.
End Terminal_and_EmptyProd.

(* Section Terminal_from_Lims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)
(* Require Import UniMath.CategoryTheory.limits.graphs.limits. *)
(* Require Import UniMath.CategoryTheory.opp_precat. *)

(* Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op"). *)

(* Context {C : precategory}. *)

(* Definition empty_graph : graph. *)
(* Proof. *)
(*   exists empty. *)
(*   exact (fun _ _ => empty). *)
(* Defined. *)

(* Definition termDiagram : diagram empty_graph C^op. *)
(* Proof. *)
(* exists fromempty. *)
(* intros u; induction u. *)
(* Defined. *)

(* Definition termCone (c : C) : cone termDiagram c. *)
(* Proof. *)
(* simple refine (mk_cone _ _); intro u; induction u. *)
(* Defined. *)

(* Lemma Terminal_from_Lims : Lims C -> Terminal C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ termDiagram); intros cc iscc; destruct cc as [c cc]; simpl in *. *)
(* apply (mk_Terminal c); apply mk_isTerminal; intros b. *)
(* case (iscc _ (termCone b)); intros f Hf; destruct f as [f fcomm]. *)
(* apply (tpair _ f); intro g. *)
(* simple refine (let X : ∑ x : b --> c, *)
(*                        ∏ v, coconeIn cc v · x = coconeIn (termCone b) v := _ in _). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Terminal_from_Lims. *)