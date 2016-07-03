(* Direct definition of initial object *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section def_initial.

Variable C : precategory.

Definition isInitial (a : C) : UU := forall b : C, iscontr (a --> b).

Definition Initial : UU := total2 (fun a => isInitial a).

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

Definition mk_isInitial (a : C) (H : ∀ (b : C), iscontr (a --> b)) :
  isInitial a.
Proof.
  exact H.
Defined.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) :
   is_isomorphism (InitialArrow O O').
Proof.
  apply (is_iso_qinv _ (InitialArrow O' O)).
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
    assert (H : forall i : empty, C⟦fromempty i, b⟧) by
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
(*   exact (fun _ _ => empty). *)
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
(* transparent assert (X : (Σ x : c --> b, ∀ v, *)
(*                        coconeIn cc v ;; x = coconeIn (initCocone b) v)). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Initial_from_Colims. *)

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section InitialFunctorCat.

Variable C D : precategory.
Variable ID : Initial D.
Variable hsD : has_homsets D.

Definition Initial_functor_precat : Initial [C, D, hsD].
Proof.
use mk_Initial.
- mkpair.
  + mkpair.
    * intros c; apply (InitialObject ID).
    * simpl; intros a b f; apply (InitialArrow ID).
  + abstract (split;
               [ intro a; apply pathsinv0, InitialEndo_is_identity
               | intros a b c f g; apply pathsinv0, InitialArrowUnique]).
- intros F.
  mkpair.
  + simpl.
    mkpair.
    * intro a; apply InitialArrow.
    * abstract (intros a b f; simpl;
                rewrite <- (InitialEndo_is_identity _ ID (InitialArrow ID ID)), id_left;
                apply pathsinv0, InitialArrowUnique).
  + abstract (intros α; apply (nat_trans_eq hsD); intro a; apply InitialArrowUnique).
Defined.

End InitialFunctorCat.