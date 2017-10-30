(**

Direct definition of initial object together with:

- A proof that initial object is a property in a (saturated/univalent) category ([isaprop_Initial])
- Construction of initial from the empty coproduct ([initial_from_empty_coproduct])
- Initial element in a functor precategory ([Initial_functor_precat])

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Epis.

Local Open Scope cat.

Section def_initial.

Variable C : precategory.

Definition isInitial (a : C) : UU := ∏ b : C, iscontr (a --> b).

Definition Initial : UU := total2 (λ a, isInitial a).

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

Lemma InitialArrowEq (O : Initial) (a : C) (f g : O --> a) : f = g.
Proof.
rewrite (InitialArrowUnique _ _ f), (InitialArrowUnique _ _ g).
apply idpath.
Qed.

Definition mk_Initial (a : C) (H : isInitial a) : Initial.
Proof.
  exists a.
  exact H.
Defined.

Definition mk_isInitial (a : C) (H : ∏ (b : C), iscontr (a --> b)) :
  isInitial a.
Proof.
  exact H.
Defined.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) :
   is_iso (InitialArrow O O').
Proof.
  apply (is_iso_qinv _ (InitialArrow O' O)).
  split; apply pathsinv0;
   apply InitialEndo_is_identity.
Defined.

Definition iso_Initials (O O' : Initial) : iso O O' :=
   tpair _ (InitialArrow O O') (isiso_from_Initial_to_Initial O O') .

Definition hasInitial := ishinh Initial.

(** * Being initial is a property in a (saturated/univalent) category *)
Section Initial_Unique.

Hypothesis H : is_univalent C.

Lemma isaprop_Initial : isaprop Initial.
Proof.
  apply invproofirrelevance.
  intros O O'.
  apply (total2_paths_f (isotoid _ H (iso_Initials O O')) ).
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

Section Initial_and_EmptyCoprod.
  Require Import UniMath.CategoryTheory.limits.coproducts.

  (** Construct Initial from empty arbitrary coproduct. *)
  Definition initial_from_empty_coproduct (C : precategory):
    CoproductCocone empty C fromempty -> Initial C.
  Proof.
    intros X.
    refine (mk_Initial (CoproductObject _ _ X) _).
    refine (mk_isInitial _ _).
    intros b.
    assert (H : ∏ i : empty, C⟦fromempty i, b⟧) by
        (intros i; apply (fromempty i)).
    apply (iscontrpair (CoproductArrow _ _ X H)); intros t.
    apply CoproductArrowUnique; intros i; apply (fromempty i).
  Defined.
End Initial_and_EmptyCoprod.

(* Section Initial_from_Colims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)

(* Variable C : precategory. *)

(* Definition empty_graph : graph. *)
(* Proof. *)
(*   exists empty. *)
(*   exact (λ _ _, empty). *)
(* Defined. *)

(* Definition initDiagram : diagram empty_graph C. *)
(* Proof. *)
(* exists fromempty. *)
(* intros u; induction u. *)
(* Defined. *)

(* Definition initCocone (b : C) : cocone initDiagram b. *)
(* Proof. *)
(* simple refine (mk_cocone _ _); intros u; induction u. *)
(* Defined. *)

(* Lemma Initial_from_Colims : Colims C -> Initial C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ initDiagram); intros cc iscc; destruct cc as [c cc]. *)
(* apply (mk_Initial c); apply mk_isInitial; intros b. *)
(* case (iscc _ (initCocone b)); intros f Hf; destruct f as [f fcomm]. *)
(* apply (tpair _ f); intro g. *)
(* transparent assert (X : (∑ x : c --> b, ∏ v, *)
(*                        coconeIn cc v · x = coconeIn (initCocone b) v)). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Initial_from_Colims. *)

(** * Construction of initial object in a functor category *)
Section InitialFunctorCat.

Variables (C D : precategory) (ID : Initial D) (hsD : has_homsets D).

Definition Initial_functor_precat : Initial [C, D, hsD].
Proof.
use mk_Initial.
- use mk_functor.
  + mkpair.
    * intros c; apply (InitialObject ID).
    * simpl; intros a b f; apply (InitialArrow ID).
  + split.
    * intro a; apply pathsinv0, InitialEndo_is_identity.
    * intros a b c f g; apply pathsinv0, InitialArrowUnique.
- intros F.
  mkpair.
  + use mk_nat_trans; simpl.
    * intro a; apply InitialArrow.
    * intros a b f; simpl.
      rewrite <- (InitialEndo_is_identity _ ID (InitialArrow ID ID)), id_left.
      now apply pathsinv0, InitialArrowUnique.
  + abstract (intros α; apply (nat_trans_eq hsD); intro a; apply InitialArrowUnique).
Defined.

End InitialFunctorCat.

(** Morphisms to the initial object are epis *)
Section epis_initial.

Context {C : precategory} (IC : Initial C).

Lemma to_initial_isEpi (a : C) (f : C⟦a,IC⟧) : isEpi f.
Proof.
apply mk_isEpi; intros b g h H.
now apply InitialArrowEq.
Qed.

End epis_initial.