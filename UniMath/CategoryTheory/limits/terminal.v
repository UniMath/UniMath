(**

Direct definition of terminal object together with:

- A proof that the terminal object is a property in a (saturated/univalent) category ([isaprop_Terminal])
- Construction of the terminal object from the empty product ([terminal_from_empty_product])


*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

Section def_terminal.

Context {C : precategory}.

Definition isTerminal (b : C) : UU := ∏ a : C, iscontr (a --> b).

Lemma isaprop_isTerminal (b : C)
  : isaprop (isTerminal b).
Proof.
  apply impred_isaprop
  ; intro
  ; apply isapropiscontr.
Qed.

Definition Terminal : UU := ∑ a, isTerminal a.

Definition TerminalObject (T : Terminal) : C := pr1 T.
Coercion TerminalObject : Terminal >-> ob.

Definition TerminalArrow (T : Terminal) (b : C) : b --> T := pr1 (pr2 T b).

Lemma TerminalArrowUnique {T : Terminal} {a : C} (f : C⟦a,TerminalObject T⟧) :
  f = TerminalArrow T _.
Proof.
exact (pr2 (pr2 T _ ) _ ).
Qed.

Lemma TerminalEndo_is_identity {T : Terminal} (f : T --> T) : f = identity T.
Proof.
apply proofirrelevancecontr, (pr2 T T).
Qed.

Lemma TerminalArrowEq {T : Terminal} {a : C} (f g : a --> T) : f = g.
Proof.
now rewrite (TerminalArrowUnique f), (TerminalArrowUnique g).
Qed.

Definition make_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
  exists b; exact H.
Defined.

Definition make_isTerminal (b : C) (H : ∏ (a : C), iscontr (a --> b)) :
  isTerminal b.
Proof.
  exact H.
Defined.

Lemma isziso_from_Terminal_to_Terminal (T T' : Terminal) :
   is_z_isomorphism (TerminalArrow T T').
Proof.
 exists (TerminalArrow T' T).
 now split; apply TerminalEndo_is_identity.
Defined.

Definition z_iso_Terminals (T T' : Terminal) : z_iso T T' :=
  TerminalArrow T' T,,isziso_from_Terminal_to_Terminal T' T.

Definition hasTerminal := ishinh Terminal.

End def_terminal.

Arguments Terminal : clear implicits.
Arguments isTerminal : clear implicits.
Arguments TerminalObject {_} _.
Arguments TerminalArrow {_} _ _.
Arguments TerminalArrowUnique {_} _ _ _.
Arguments make_isTerminal {_} _ _ _.
Arguments make_Terminal {_} _ _.


Section Terminal_Unique.

Context (C : category) (H : is_univalent C).

Lemma isaprop_Terminal : isaprop (Terminal C).
Proof.
  apply invproofirrelevance.
  intros T T'.
  apply (total2_paths_f (isotoid _ H (z_iso_Terminals T T')) ).
  apply isaprop_isTerminal.
Qed.

End Terminal_Unique.


Section Terminal_and_EmptyProd.

  (** Construct Terminal from empty arbitrary product. *)
  Definition terminal_from_empty_product (C : category) :
    Product ∅ C fromempty -> Terminal C.
  Proof.
    intros X.
    use (make_Terminal (ProductObject _ C X)).
    use make_isTerminal.
    intros a.
    assert (H : ∏ i : ∅, C⟦a, fromempty i⟧) by
        (intros i; apply (fromempty i)).
    apply (make_iscontr (ProductArrow _ _ X H)).
    abstract (intros t; apply ProductArrowUnique; intros i; apply (fromempty i)).
  Defined.

  Section TerminalToProduct.

    Context {C : category}.
    Context (T : Terminal C).
    Context (c : ∅ → C).

    Definition terminal_product_object
      : C
      := T.

    Definition terminal_product_projection
      (i : ∅)
      : C⟦terminal_product_object, c i⟧.
    Proof.
      induction i.
    Defined.

    Section Arrow.

      Context (c' : C).
      Context (cone' : ∏ i, C⟦c', c i⟧).

      Definition terminal_product_arrow
        : C⟦c', terminal_product_object⟧
        := TerminalArrow T c'.

      Lemma terminal_product_arrow_commutes
        (i : ∅)
        : terminal_product_arrow · terminal_product_projection i = cone' i.
      Proof.
        induction i.
      Qed.

      Lemma terminal_product_arrow_unique
        (t : ∑ k, ∏ i : ∅, k · terminal_product_projection i = cone' i)
        : t = terminal_product_arrow ,, terminal_product_arrow_commutes.
      Proof.
        use subtypePairEquality.
        {
          intro i.
          apply impred_isaprop.
          intro.
          apply homset_property.
        }
        apply TerminalArrowUnique.
      Qed.

    End Arrow.

    Definition terminal_is_product
      : isProduct _ _ _ terminal_product_object terminal_product_projection.
    Proof.
      use (make_isProduct _ _ (homset_property C)).
      intros c' cone'.
      use make_iscontr.
      - use tpair.
        + exact (terminal_product_arrow c').
        + exact (terminal_product_arrow_commutes c' cone').
      - exact (terminal_product_arrow_unique c' cone').
    Defined.

    Definition Terminal_is_empty_product
      : Product ∅ C c.
    Proof.
      use make_Product.
      - exact terminal_product_object.
      - exact terminal_product_projection.
      - exact terminal_is_product.
    Defined.

  End TerminalToProduct.

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
(* simple refine (make_cone _ _); intro u; induction u. *)
(* Defined. *)

(* Lemma Terminal_from_Lims : Lims C -> Terminal C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ termDiagram); intros cc iscc; destruct cc as [c cc]; simpl in *. *)
(* apply (make_Terminal c); apply make_isTerminal; intros b. *)
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

Context (C D : category) (ID : Terminal D).

Definition Terminal_functor_precat : Terminal [C,D].
Proof.
use make_Terminal.
- exact (constant_functor _ _ ID).
- intros F.
  use tpair.
  + use make_nat_trans.
    * intro a; apply TerminalArrow.
    * abstract (intros a b f; apply TerminalArrowEq).
  + abstract (intros α; apply (nat_trans_eq D); intro a; apply TerminalArrowUnique).
Defined.

End TerminalFunctorCat.

(** Morphisms from the terminal object are monic *)
Section monics_terminal.

Context {C : category} (TC : Terminal C).

Lemma from_terminal_isMonic (a : C) (f : TC --> a) : isMonic f.
Proof.
apply make_isMonic; intros b g h H.
now apply TerminalArrowEq.
Qed.

End monics_terminal.

Definition iso_to_Terminal
           {C : category}
           (T : Terminal C)
           (x : C)
           (i : z_iso T x)
  : isTerminal C x.
Proof.
  intros w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (!(id_right _) @ _ @ id_right _) ;
       rewrite <- !(z_iso_after_z_iso_inv i) ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - exact (TerminalArrow T w · i).
Defined.
