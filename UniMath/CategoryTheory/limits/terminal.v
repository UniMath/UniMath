(**

Direct definition of terminal object together with:

- A proof that the terminal object is a property in a (saturated/univalent) category ([isaprop_Terminal])
- Construction of the terminal object from the empty product ([terminal_from_empty_product])


*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

Section def_terminal.

Variable C : precategory.

Definition isTerminal (b : C) : UU := ∏ a : C, iscontr (a --> b).

Definition Terminal : UU := total2 (λ a, isTerminal a).

Definition TerminalObject (T : Terminal) : C := pr1 T.
Coercion TerminalObject : Terminal >-> ob.

Definition TerminalArrow (T : Terminal) (b : C) : b --> T :=  pr1 (pr2 T b).

Lemma TerminalEndo_is_identity (T : Terminal) (f : T --> T) : identity T = f.
Proof.
now apply proofirrelevance, isapropifcontr, (pr2 T T).
Qed.

Lemma TerminalArrowUnique (T : Terminal) (a : C)
  (f : C⟦a,TerminalObject T⟧) : f = TerminalArrow T _.
Proof.
exact (pr2 (pr2 T _ ) _ ).
Defined.

Lemma ArrowsToTerminal (T : Terminal) (a : C) (f g : a --> T) : f = g.
Proof.
now rewrite (TerminalArrowUnique _ _ f), (TerminalArrowUnique _ _ g).
Qed.

Definition mk_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
  exists b; exact H.
Defined.

Definition mk_isTerminal (b : C) (H : ∏ (a : C), iscontr (a --> b)) :
  isTerminal b.
Proof.
  exact H.
Defined.

Lemma isiso_from_Terminal_to_Terminal (T T' : Terminal) :
   is_iso (TerminalArrow T T').
Proof.
apply (is_iso_qinv _ (TerminalArrow T' T)).
now split; apply pathsinv0, TerminalEndo_is_identity.
Defined.

Definition iso_Terminals (T T' : Terminal) : iso T T' :=
   tpair _ (TerminalArrow T' T) (isiso_from_Terminal_to_Terminal T' T) .

Definition hasTerminal := ishinh Terminal.

Section Terminal_Unique.

Hypothesis H : is_univalent C.

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
(*   exact (λ _ _, empty). *)
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

(** * Construction of terminal object in a functor category *)
Section TerminalFunctorCat.

Variables (C D : precategory) (ID : Terminal D) (hsD : has_homsets D).

Definition Terminal_functor_precat : Terminal [C,D,hsD].
Proof.
use mk_Terminal.
- use mk_functor.
  + mkpair.
    * intros c; apply (TerminalObject ID).
    * simpl; intros a b f; apply (TerminalArrow ID).
  + split.
    * intro a; apply pathsinv0, TerminalEndo_is_identity.
    * intros a b c f g; apply pathsinv0, TerminalArrowUnique.
- intros F.
  mkpair.
  + use mk_nat_trans; simpl.
    * intro a; apply TerminalArrow.
    * intros a b f; simpl.
      rewrite <- (TerminalEndo_is_identity _ ID (TerminalArrow ID)), id_right.
      apply TerminalArrowUnique.
  + abstract (intros α; apply (nat_trans_eq hsD); intro a; apply TerminalArrowUnique).
Defined.

End TerminalFunctorCat.

(** Morphisms from the terminal object are monic *)
Section monics_terminal.

Context {C : precategory} (TC : Terminal C).

Lemma from_terminal_isMonic (a : C) (f : C⟦TC,a⟧) : isMonic f.
Proof.
apply mk_isMonic; intros b g h H.
now apply ArrowsToTerminal.
Qed.

End monics_terminal.